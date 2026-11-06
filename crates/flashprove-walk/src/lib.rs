//! Native sequential walk of an H821 proof chain.
//!
//! The cursor decides every read size from the plan, the format's rules and
//! its own Fiat-Shamir draws:
//!
//! * a round's prover message: `message_bytes` of the plan entry (R4.3);
//! * a nonce: `nonce_bytes` of the plan, only if the entry has work bits;
//! * the kind hashed into each round call: from the round's name (R14.11);
//! * roots: a message with r roots and no other items is r digests, and tree
//!   numbers follow the order of receipt (R7.13, `TreeBook::enter`);
//! * positions: the first words of a kind-4 round's draw (R6.10), as many as
//!   the entry's `draw_positions`, from [0, 2^log_n);
//! * an opening's size: m (8 W + s) + 32 g from shape and list (R7.8, R7.9).
//!
//! It never reads a C++ offset. One input is NOT yet native: the opening
//! schedule ([`OpeningSchedule`]), which says which trees are opened after
//! which positions round and gives their column widths. In the reference
//! these follow from the statement's oracle notices (`lay_trees`, blocks/iop/
//! context.h) and the protocol code; deriving them is stage D7. The walk
//! verifies every opening cryptographically against the root the chain
//! received. A wrong tree number, depth, total width or round makes it
//! reject. A wrong split of the width into parts, or a wrong `log_n_zk`, does
//! NOT: the leaf hash sees only the flat column, so those two fields only
//! change how columns are interpreted, which the algebraic checks (D9) enforce.
//!
//! Not a verifier: no algebraic check is made on the opened columns, the
//! answers or the scalars, and only one chain is walked.

use flashprove_merkle::{
    opening_bytes, receive_opening, MerkleError, OracleTreeShape, PositionList, Session,
};
use flashprove_transcript::first_query::{Parameters, Round};
use flashprove_transcript::{first_value, run_value, Chain, Digest, RoundKind, TranscriptError};
use std::collections::BTreeMap;
use std::fmt;

pub const PROOF_MAGIC: &[u8; 8] = b"CPPFH821";
/// Magic, the stored-copy number (u32), the first chain's 32 random bytes.
pub const PROOF_HEAD_BYTES: usize = 44;
pub const MAX_PROOF_BYTES: usize = 512 * 1024 * 1024;
const MAX_EXPANDED_ROUNDS: u64 = 1_000_000;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WalkError {
    Head(&'static str),
    Truncated {
        what: String,
        at: usize,
        needed: usize,
    },
    UnknownRoundName(String),
    NotARound(String),
    Plan(String),
    RootLayout {
        round: u64,
        message_bytes: u64,
        roots: u64,
    },
    Transcript {
        round: u64,
        error: TranscriptError,
    },
    Positions {
        round: u64,
        error: MerkleError,
    },
    Schedule(String),
    NoRoot {
        round: u64,
        tree: u32,
    },
    Opening {
        round: u64,
        tree: u32,
        offset: usize,
        error: MerkleError,
    },
    TooLarge,
}
impl fmt::Display for WalkError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for WalkError {}

/// R14.11: the kind follows from the name. `RECORD` is not a round.
pub fn kind_of_name(name: &str) -> Result<RoundKind, WalkError> {
    use RoundKind::*;
    Ok(match name {
        "BAT" | "BAT-sigma" | "PSC round" | "PSC Y" | "ZERO" | "LINE" | "LKP shift" | "JOIN"
        | "LKP" | "FOLD round" | "BASE lambda" | "LIN point" | "LIN zeta" | "LINK point"
        | "LINK phi" => Algebraic,
        "PSC epsilon" | "FOLD epsilon" => Epsilon,
        "SEND seed" => Seed,
        "LOC" | "CS" | "BASE" | "LINK" => Positions,
        "RNG" => Bits,
        "SEAL" => Seal,
        "SEND answer" | "SPLIT" | "PSC values" | "REPLY" | "LAST" => Empty,
        "RECORD" => return Err(WalkError::NotARound(name.into())),
        _ => return Err(WalkError::UnknownRoundName(name.into())),
    })
}

/// One tree to open after a positions round. Plan data (stage D7 stand-in).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScheduledOpening {
    /// The number of rounds closed when the opening is read: a kind-4 round.
    pub after_round: u64,
    pub tree: u32,
    pub log_n: u32,
    pub log_n_zk: u32,
    pub main_symbols: Vec<usize>,
    pub mask_symbols: Vec<usize>,
}
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct OpeningSchedule {
    pub by_round: BTreeMap<u64, Vec<ScheduledOpening>>,
}
impl OpeningSchedule {
    /// Text form, one opening per line, `#` comments:
    /// `after_round=K tree=T log_n=A log_n_zk=B main=w,w mask=w,w`
    pub fn parse(text: &str) -> Result<Self, WalkError> {
        let bad = |l: usize, m: &str| WalkError::Schedule(format!("line {}: {m}", l + 1));
        let mut by_round: BTreeMap<u64, Vec<ScheduledOpening>> = BTreeMap::new();
        let mut seen_trees = std::collections::BTreeSet::new();
        for (l, line) in text.lines().enumerate() {
            let line = line.split('#').next().unwrap_or("").trim();
            if line.is_empty() {
                continue;
            }
            let mut f: BTreeMap<&str, &str> = BTreeMap::new();
            for kv in line.split_whitespace() {
                let (k, v) = kv
                    .split_once('=')
                    .ok_or_else(|| bad(l, "field without '='"))?;
                if f.insert(k, v).is_some() {
                    return Err(bad(l, "duplicate field"));
                }
            }
            let keys: Vec<&str> = f.keys().copied().collect();
            if keys != ["after_round", "log_n", "log_n_zk", "main", "mask", "tree"] {
                return Err(bad(
                    l,
                    "expected exactly after_round, tree, log_n, log_n_zk, main, mask",
                ));
            }
            let num = |k: &str| {
                f[k].parse::<u64>()
                    .map_err(|_| bad(l, "not an unsigned integer"))
            };
            let list = |k: &str| -> Result<Vec<usize>, WalkError> {
                f[k].split(',')
                    .map(|x| x.parse::<usize>().map_err(|_| bad(l, "bad width list")))
                    .collect()
            };
            let o = ScheduledOpening {
                after_round: num("after_round")?,
                tree: u32::try_from(num("tree")?).map_err(|_| bad(l, "tree number"))?,
                log_n: u32::try_from(num("log_n")?).map_err(|_| bad(l, "log_n"))?,
                log_n_zk: u32::try_from(num("log_n_zk")?).map_err(|_| bad(l, "log_n_zk"))?,
                main_symbols: list("main")?,
                mask_symbols: list("mask")?,
            };
            // A tree is opened once in this chain's schedule (each first-chain tree is
            // read by one test); a second opening needs a reason the schedule cannot give.
            if !seen_trees.insert(o.tree) {
                return Err(bad(l, "a tree scheduled twice"));
            }
            by_round.entry(o.after_round).or_default().push(o);
        }
        for v in by_round.values() {
            if v.windows(2).any(|w| w[0].tree >= w[1].tree) {
                return Err(WalkError::Schedule(
                    "trees after one round must be in increasing order".into(),
                ));
            }
        }
        Ok(Self { by_round })
    }
    pub fn len(&self) -> usize {
        self.by_round.values().map(Vec::len).sum()
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RoundRecord {
    pub round: u64,
    pub name: String,
    pub kind: RoundKind,
    pub message_offset: usize,
    pub message_bytes: usize,
    pub nonce_offset: Option<usize>,
    pub rho: Digest,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OpeningRecord {
    pub after_round: u64,
    pub tree: u32,
    pub offset: usize,
    pub bytes: usize,
    pub root: Digest,
    pub list: Vec<u64>,
    pub draws: usize,
    pub run: Digest,
    pub parameters: Digest,
    pub given: usize,
}
#[derive(Debug, Clone)]
pub struct ChainWalk {
    pub label: u64,
    pub run: Digest,
    pub configuration: Digest,
    pub rho0: Digest,
    pub rounds: Vec<RoundRecord>,
    pub openings: Vec<OpeningRecord>,
    pub roots: Vec<Digest>,
    /// The cursor after the chain's last planned round and openings.
    pub end: usize,
    pub merkle_vertices: usize,
}

struct Cursor<'a> {
    b: &'a [u8],
    at: usize,
}
impl<'a> Cursor<'a> {
    fn take(&mut self, n: usize, what: impl Fn() -> String) -> Result<&'a [u8], WalkError> {
        let end = self.at.checked_add(n).ok_or(WalkError::TooLarge)?;
        let s = self
            .b
            .get(self.at..end)
            .ok_or_else(|| WalkError::Truncated {
                what: what(),
                at: self.at,
                needed: n,
            })?;
        self.at = end;
        Ok(s)
    }
}

/// The proof head: stored copy number and the first chain's random bytes.
pub fn read_head(proof: &[u8]) -> Result<(u32, Digest), WalkError> {
    if proof.len() > MAX_PROOF_BYTES {
        return Err(WalkError::TooLarge);
    }
    if proof.len() < PROOF_HEAD_BYTES || &proof[..8] != PROOF_MAGIC {
        return Err(WalkError::Head("missing CPPFH821 head"));
    }
    let copy = u32::from_le_bytes(proof[8..12].try_into().expect("4 bytes"));
    let salt: Digest = proof[12..44].try_into().expect("32 bytes");
    Ok((copy, salt))
}

/// The trusted inputs of one chain's walk. `plan` and `statement` are the
/// chain's first-query parameters and statement, audited against the public
/// files by the caller (stage D7 will derive them natively).
pub struct ChainInputs<'a> {
    pub label: u64,
    pub plan: &'a Parameters,
    pub parameters_digest: Digest,
    pub statement: &'a [u8],
    pub configuration: Digest,
    pub schedule: &'a OpeningSchedule,
}

fn expand(rounds: &[Round]) -> Result<Vec<&Round>, WalkError> {
    let total = rounds
        .iter()
        .try_fold(0_u64, |a, r| a.checked_add(r.count))
        .ok_or(WalkError::TooLarge)?;
    if total > MAX_EXPANDED_ROUNDS {
        return Err(WalkError::TooLarge);
    }
    let mut v = Vec::with_capacity(total as usize);
    for r in rounds {
        for _ in 0..r.count {
            v.push(r);
        }
    }
    Ok(v)
}

/// Walks the first chain, which starts right after the proof head.
pub fn walk_first_chain(proof: &[u8], inputs: &ChainInputs<'_>) -> Result<ChainWalk, WalkError> {
    let (_, salt) = read_head(proof)?;
    walk_chain(proof, PROOF_HEAD_BYTES, &salt, inputs)
}

pub fn walk_chain(
    proof: &[u8],
    start: usize,
    random_bytes: &Digest,
    inputs: &ChainInputs<'_>,
) -> Result<ChainWalk, WalkError> {
    let plan = inputs.plan;
    let tr = |round: u64| move |error: TranscriptError| WalkError::Transcript { round, error };
    let run = run_value(inputs.label, &inputs.parameters_digest, random_bytes).map_err(tr(0))?;
    let rho0 = first_value(
        inputs.label,
        &inputs.parameters_digest,
        inputs.statement,
        Some(&run),
    )
    .map_err(tr(0))?;
    let salt_bytes =
        usize::try_from(plan.salt_bytes).map_err(|_| WalkError::Plan("salt".into()))?;
    let nonce_bytes =
        usize::try_from(plan.nonce_bytes).map_err(|_| WalkError::Plan("nonce".into()))?;
    if !(1..=8).contains(&nonce_bytes) {
        return Err(WalkError::Plan("nonce width".into()));
    }
    let expanded = expand(&plan.rounds)?;
    for k in inputs.schedule.by_round.keys() {
        let e = usize::try_from(*k)
            .ok()
            .and_then(|k| k.checked_sub(1))
            .and_then(|i| expanded.get(i));
        match e {
            Some(e) if kind_of_name(&e.name)? == RoundKind::Positions => {}
            _ => {
                return Err(WalkError::Schedule(format!(
                    "round {k} is no positions round of this plan"
                )))
            }
        }
    }

    let mut chain = Chain::new(inputs.label, rho0).map_err(tr(0))?;
    let mut cur = Cursor {
        b: proof,
        at: start,
    };
    let mut session = Session::default();
    let mut rounds = Vec::with_capacity(expanded.len());
    let mut openings = Vec::new();
    let mut roots: Vec<Digest> = Vec::new();

    for (i, entry) in expanded.iter().enumerate() {
        let rno = i as u64 + 1;
        let kind = kind_of_name(&entry.name)?;
        let mlen = usize::try_from(entry.message_bytes).map_err(|_| WalkError::TooLarge)?;
        let moff = cur.at;
        let message = cur.take(mlen, || format!("round {rno} message"))?;
        if entry.roots > 0 {
            // Only the layout "the message is its roots" is supported natively;
            // anything else fails closed until the message layout is ported.
            if entry.answers != 0
                || entry.message_bytes != entry.roots.checked_mul(32).ok_or(WalkError::TooLarge)?
            {
                return Err(WalkError::RootLayout {
                    round: rno,
                    message_bytes: entry.message_bytes,
                    roots: entry.roots,
                });
            }
            for c in message.chunks_exact(32) {
                roots.push(c.try_into().expect("32 bytes"));
            }
        }
        let work = u8::try_from(entry.work).map_err(|_| WalkError::Plan("work bits".into()))?;
        let (nonce, noff) = if work > 0 {
            let at = cur.at;
            let raw = cur.take(nonce_bytes, || format!("round {rno} nonce"))?;
            let mut b = [0_u8; 8];
            b[..nonce_bytes].copy_from_slice(raw);
            (u64::from_le_bytes(b), Some(at))
        } else {
            (0, None)
        };
        let mut draw = chain
            .close_round(message, kind, work, nonce)
            .map_err(tr(rno))?;
        rounds.push(RoundRecord {
            round: rno,
            name: entry.name.clone(),
            kind,
            message_offset: moff,
            message_bytes: mlen,
            nonce_offset: noff,
            rho: *chain.value(),
        });

        let Some(scheduled) = inputs.schedule.by_round.get(&rno) else {
            if kind == RoundKind::Positions {
                // Positions are drawn to be opened; a schedule that opens nothing
                // here is not one this walk can trust.
                return Err(WalkError::Schedule(format!(
                    "positions round {rno} ({}) has no scheduled opening",
                    entry.name
                )));
            }
            continue;
        };
        // R6.10: the positions come first in a kind-4 round's draw.
        let log_n = u32::try_from(entry.log_n).map_err(|_| WalkError::Plan("log_n".into()))?;
        let width = u8::try_from(entry.log_n).map_err(|_| WalkError::Plan("log_n".into()))?;
        if entry.positions == 0 || entry.positions > 1 << 20 {
            return Err(WalkError::Plan(format!("round {rno}: draw_positions")));
        }
        let mut draws = Vec::with_capacity(entry.positions as usize);
        for _ in 0..entry.positions {
            draws.push(draw.position(width).map_err(tr(rno))?);
        }
        let list = PositionList::from_draws(draws, log_n)
            .map_err(|error| WalkError::Positions { round: rno, error })?;
        for s in scheduled {
            let root = *roots.get(s.tree as usize).ok_or(WalkError::NoRoot {
                round: rno,
                tree: s.tree,
            })?;
            let shape = OracleTreeShape {
                log_n: s.log_n,
                log_n_zk: s.log_n_zk,
                main_symbols: s.main_symbols.clone(),
                mask_symbols: s.mask_symbols.clone(),
                tree_number: s.tree,
                salt_bytes,
                stored: false,
                run,
                parameters: inputs.configuration,
            };
            let at = cur.at;
            let err = |error| WalkError::Opening {
                round: rno,
                tree: s.tree,
                offset: at,
                error,
            };
            if s.log_n > log_n {
                return Err(err(MerkleError::InvalidList(
                    "tree deeper than its list's range",
                )));
            }
            let own = list.for_tree(s.log_n).map_err(err)?;
            let need = opening_bytes(&shape, &own).map_err(err)?;
            let (_, used) =
                receive_opening(&proof[at..], &root, &shape, &own, &mut session).map_err(err)?;
            debug_assert_eq!(used, need);
            cur.at += used;
            openings.push(OpeningRecord {
                after_round: rno,
                tree: s.tree,
                offset: at,
                bytes: used,
                root,
                list: own.all().to_vec(),
                draws: own.draws().len(),
                run,
                parameters: inputs.configuration,
                given: flashprove_merkle::tree_given_count(s.log_n, &own).map_err(err)?,
            });
        }
    }
    let merkle_vertices = roots.iter().map(|r| session.record(r).vertices()).sum();
    Ok(ChainWalk {
        label: inputs.label,
        run,
        configuration: inputs.configuration,
        rho0,
        rounds,
        openings,
        roots,
        end: cur.at,
        merkle_vertices,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn r14_11_has_29_rounds() {
        let names = [
            "BAT",
            "BAT-sigma",
            "PSC round",
            "PSC Y",
            "ZERO",
            "LINE",
            "LKP shift",
            "JOIN",
            "LKP",
            "FOLD round",
            "BASE lambda",
            "LIN point",
            "LIN zeta",
            "LINK point",
            "LINK phi",
            "PSC epsilon",
            "FOLD epsilon",
            "SEND seed",
            "LOC",
            "CS",
            "BASE",
            "LINK",
            "RNG",
            "SEAL",
            "SEND answer",
            "SPLIT",
            "PSC values",
            "REPLY",
            "LAST",
        ];
        assert_eq!(names.len(), 29);
        for n in names {
            kind_of_name(n).unwrap();
        }
        assert!(matches!(
            kind_of_name("RECORD"),
            Err(WalkError::NotARound(_))
        ));
        assert!(matches!(
            kind_of_name("SEND"),
            Err(WalkError::UnknownRoundName(_))
        ));
        assert_eq!(kind_of_name("LOC").unwrap(), RoundKind::Positions);
        assert_eq!(kind_of_name("SEAL").unwrap(), RoundKind::Seal);
        assert_eq!(kind_of_name("LAST").unwrap(), RoundKind::Empty);
    }

    #[test]
    fn schedule_rejects_malformed() {
        let ok = "after_round=5 tree=0 log_n=3 log_n_zk=0 main=2 mask=0\n# c\n";
        assert_eq!(OpeningSchedule::parse(ok).unwrap().len(), 1);
        for bad in [
            "after_round=5 tree=0 log_n=3 log_n_zk=0 main=2",
            "after_round=5 tree=0 log_n=3 log_n_zk=0 main=2 mask=0 extra=1",
            "after_round=5 tree=0 log_n=3 log_n_zk=0 main=2 mask=0\nafter_round=6 tree=0 log_n=3 log_n_zk=0 main=2 mask=0",
            "after_round=5 tree=1 log_n=3 log_n_zk=0 main=2 mask=0\nafter_round=5 tree=0 log_n=3 log_n_zk=0 main=2 mask=0",
            "after_round=x tree=0 log_n=3 log_n_zk=0 main=2 mask=0",
        ] {
            assert!(OpeningSchedule::parse(bad).is_err(), "{bad}");
        }
    }
}
