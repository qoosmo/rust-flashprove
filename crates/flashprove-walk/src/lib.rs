//! Native sequential walk of an H821 proof file: every chain, every round,
//! the place in the binding tree, and every Merkle opening, to the last byte.
//!
//! The cursor decides every read size from the plan, the format's rules and
//! its own Fiat-Shamir draws:
//!
//! * a round's prover message: `message_bytes` of the plan entry (R4.3);
//! * a nonce: `nonce_bytes` of the plan, after the message, only with work bits;
//! * the kind hashed into each round call: from the round's name (R14.11);
//! * roots: after the message's answers (R8.3), in tree order (R8.6), before a
//!   kind-2 round's hiding sum (R8.4); received in order (R7.13);
//! * positions: the first words of a kind-4 round's draw (R6.10);
//! * a seal: the four words drawn by a kind-6 round (R6.8);
//! * an opening's size: m (8 W + s) + 32 g from shape and list (R7.8, R7.9);
//! * the place: the request's slot, salt and path in the binding tree (R7.18).
//!
//! It never reads a C++ offset. Not yet native (stage D7): each chain's
//! serialized first-query parameters and statement (checked here item by item
//! against what this walk computes and against each other), and the opening
//! schedule ([`OpeningSchedule`]). Every scheduled opening is checked against
//! a root that this walk received or derived itself. A wrong tree, depth,
//! total width, salt, root source or round makes it reject; a wrong split of
//! the width into parts or a wrong `log_n_zk` does not (the leaf hash sees
//! only the flat column): D7 must derive those and D9 enforces them.
//!
//! Not a verifier: no algebraic check is made on the opened columns, the
//! answers or the scalars.

pub mod shared_chain;
use flashprove_field::Fp;
use flashprove_merkle::{
    leaf_salt_at, opening_bytes, receive_opening, tree_given_count, MerkleError, OracleTreeShape,
    PositionList, Session,
};
use flashprove_transcript::first_query::{
    parameters_digest, parse_parameters, Item, Parameters, QueryError, Round,
};
use flashprove_transcript::{
    configuration_digest, first_value, h, run_value, Chain, Digest, Draw, RoundKind,
    TranscriptError,
};
use std::collections::BTreeMap;
use std::fmt;

pub const PROOF_MAGIC: &[u8; 8] = b"CPPFH821";
/// Magic, the stored-copy number (u32), the first chain's 32 random bytes.
pub const PROOF_HEAD_BYTES: usize = 44;
pub const MAX_PROOF_BYTES: usize = 512 * 1024 * 1024;
const MAX_EXPANDED_ROUNDS: u64 = 1_000_000;

/// Chain labels of a proof file (upstream blocks/frame/heads.h).
pub const LABEL_FIRST_CHAIN: u64 = 0x4652_4d01;
pub const LABEL_PROOF_SHARED_CHAIN: u64 = 0x4652_4d03;
pub const LABEL_PROOF_SECOND_CHAIN: u64 = 0x4652_4d04;
/// Domains of the binding tree (R7.18).
pub const LEAF_BINDING: u16 = 173;
pub const BINDING_NODE: u16 = 178;
pub const SEAL_ITEM: &str = "the seal of an earlier chain";

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
    FirstQuery(String),
    RootLayout {
        chain: u64,
        round: u64,
        message_bytes: u64,
        roots: u64,
    },
    Transcript {
        chain: u64,
        round: u64,
        error: TranscriptError,
    },
    Positions {
        chain: u64,
        round: u64,
        error: MerkleError,
    },
    Schedule(String),
    NoRoot {
        chain: u64,
        round: u64,
        tree: u32,
    },
    Opening {
        chain: u64,
        round: u64,
        tree: u32,
        offset: usize,
        error: MerkleError,
    },
    Place(String),
    Linkage(String),
    NoSeal(u64),
    LeftOver {
        at: usize,
        len: usize,
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

/// Where an opened tree's root comes from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RootSource {
    /// The `index`-th root received by chain `chain` (this chain or one it follows).
    /// The leaves start from that chain's run value.
    Received { chain: u64, index: usize },
    /// The committed table named in this chain's first query (a stored tree, R7.4).
    Table,
}

/// One tree to open after a positions round. Plan data (stage D7 stand-in).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScheduledOpening {
    pub chain: u64,
    /// The number of this chain's rounds closed when the opening is read: a kind-4 round.
    pub after_round: u64,
    /// The tree number hashed into every leaf (0 for a stored tree).
    pub tree: u32,
    pub root: RootSource,
    pub log_n: u32,
    pub log_n_zk: u32,
    pub main_symbols: Vec<usize>,
    pub mask_symbols: Vec<usize>,
    /// Salt length of a stored tree; run trees use the chain's plan.
    pub salt: Option<usize>,
}
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct OpeningSchedule {
    /// (chain, after_round) -> openings in reading order.
    pub by_round: BTreeMap<(u64, u64), Vec<ScheduledOpening>>,
}
impl OpeningSchedule {
    /// Text form, one opening per line, `#` comments:
    /// `chain=HEX after_round=K tree=T root=HEX:IDX|table log_n=A log_n_zk=B main=w,.. mask=w,.. [salt=S]`
    pub fn parse(text: &str) -> Result<Self, WalkError> {
        let bad = |l: usize, m: &str| WalkError::Schedule(format!("line {}: {m}", l + 1));
        let mut by_round: BTreeMap<(u64, u64), Vec<ScheduledOpening>> = BTreeMap::new();
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
            let mut keys: Vec<&str> = f.keys().copied().collect();
            keys.retain(|k| *k != "salt");
            if keys
                != [
                    "after_round",
                    "chain",
                    "log_n",
                    "log_n_zk",
                    "main",
                    "mask",
                    "root",
                    "tree",
                ]
            {
                return Err(bad(
                    l,
                    "expected chain, after_round, tree, root, log_n, log_n_zk, main, mask [, salt]",
                ));
            }
            let num = |k: &str| {
                f[k].parse::<u64>()
                    .map_err(|_| bad(l, "not an unsigned integer"))
            };
            let hex = |s: &str| u64::from_str_radix(s, 16).map_err(|_| bad(l, "not a hex label"));
            let list = |k: &str| -> Result<Vec<usize>, WalkError> {
                f[k].split(',')
                    .map(|x| x.parse::<usize>().map_err(|_| bad(l, "bad width list")))
                    .collect()
            };
            let root = match f["root"] {
                "table" => RootSource::Table,
                r => {
                    let (c, i) = r
                        .split_once(':')
                        .ok_or_else(|| bad(l, "root is LABEL:INDEX or table"))?;
                    RootSource::Received {
                        chain: hex(c)?,
                        index: i.parse().map_err(|_| bad(l, "root index"))?,
                    }
                }
            };
            let salt = match f.get("salt") {
                Some(s) => Some(s.parse::<usize>().map_err(|_| bad(l, "salt"))?),
                None => None,
            };
            if (root == RootSource::Table) != salt.is_some() {
                return Err(bad(
                    l,
                    "a stored tree (root=table) names its salt; a run tree takes the plan's",
                ));
            }
            let o = ScheduledOpening {
                chain: hex(f["chain"])?,
                after_round: num("after_round")?,
                tree: u32::try_from(num("tree")?).map_err(|_| bad(l, "tree number"))?,
                root,
                log_n: u32::try_from(num("log_n")?).map_err(|_| bad(l, "log_n"))?,
                log_n_zk: u32::try_from(num("log_n_zk")?).map_err(|_| bad(l, "log_n_zk"))?,
                main_symbols: list("main")?,
                mask_symbols: list("mask")?,
                salt,
            };
            let v = by_round.entry((o.chain, o.after_round)).or_default();
            // A tree is opened once at one list: a leaf is opened whole (TreeBook::count_opening).
            if v.iter().any(|p| p.root == o.root) {
                return Err(bad(l, "one tree opened twice after one round"));
            }
            v.push(o);
        }
        Ok(Self { by_round })
    }
    pub fn len(&self) -> usize {
        self.by_round.values().map(Vec::len).sum()
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    pub fn for_chain(&self, chain: u64) -> impl Iterator<Item = (&u64, &Vec<ScheduledOpening>)> {
        self.by_round
            .iter()
            .filter(move |((c, _), _)| *c == chain)
            .map(|((_, r), v)| (r, v))
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
    pub chain: u64,
    pub after_round: u64,
    pub tree: u32,
    pub stored: bool,
    pub offset: usize,
    pub bytes: usize,
    pub root: Digest,
    pub list: Vec<u64>,
    pub draws: usize,
    pub run: Digest,
    pub parameters: Digest,
    pub given: usize,
    pub salt_bytes: usize,
    /// The list's draws in the order drawn, repeats included (`PositionList::draws`).
    pub draw_list: Vec<u64>,
    /// The opened columns, canonical, one per listed position in increasing order.
    pub columns: Vec<Fp>,
    pub width: usize,
}
#[derive(Debug, Clone)]
pub struct ChainWalk {
    pub label: u64,
    pub start: usize,
    pub salt_in_proof: bool,
    pub run: Digest,
    pub configuration: Digest,
    pub rho0: Digest,
    pub rounds: Vec<RoundRecord>,
    pub openings: Vec<OpeningRecord>,
    pub roots: Vec<Digest>,
    pub seal: Option<Digest>,
    /// The cursor after the chain's last planned round and openings.
    pub end: usize,
    /// Each round's verifier message, as a `Draw` positioned after the round's
    /// positions (kind 4) or seal (kind 6); `draws[k - 1]` is round k. The
    /// protocol blocks continue drawing from it in the reference's order.
    pub draws: Vec<Draw>,
}
impl ChainWalk {
    /// A fresh copy of round k's verifier message (1-based).
    pub fn draw(&self, round: u64) -> Option<Draw> {
        usize::try_from(round)
            .ok()
            .and_then(|r| r.checked_sub(1))
            .and_then(|i| self.draws.get(i))
            .cloned()
    }
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
    fn digest(&mut self, what: &str) -> Result<Digest, WalkError> {
        Ok(self
            .take(32, || what.to_string())?
            .try_into()
            .expect("32 bytes"))
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

/// A first query's statement: (name, value) items, as `Binder` writes them.
pub fn parse_items(bytes: &[u8]) -> Result<Vec<Item>, WalkError> {
    let bad = |m: &str| WalkError::FirstQuery(m.into());
    let mut at = 0;
    let mut out = Vec::new();
    let sized = |at: &mut usize| -> Result<Vec<u8>, WalkError> {
        let n = bytes.get(*at..*at + 8).ok_or_else(|| bad("short item"))?;
        let n = usize::try_from(u64::from_le_bytes(n.try_into().expect("8")))
            .map_err(|_| bad("item length"))?;
        let s = *at + 8;
        let e = s.checked_add(n).ok_or_else(|| bad("item length"))?;
        let v = bytes.get(s..e).ok_or_else(|| bad("short item"))?.to_vec();
        *at = e;
        Ok(v)
    };
    while at < bytes.len() {
        if out.len() >= 256 {
            return Err(bad("too many items"));
        }
        let name = String::from_utf8(sized(&mut at)?).map_err(|_| bad("item name not UTF-8"))?;
        let value = sized(&mut at)?;
        out.push(Item { name, value });
    }
    Ok(out)
}
fn item<'a>(items: &'a [Item], name: &str) -> Result<&'a [u8], WalkError> {
    let mut it = items.iter().filter(|i| i.name == name);
    let v = it
        .next()
        .ok_or_else(|| WalkError::FirstQuery(format!("no item '{name}'")))?;
    if it.next().is_some() {
        return Err(WalkError::FirstQuery(format!("item '{name}' twice")));
    }
    Ok(&v.value)
}
/// The commitment (root) inside a `table` item: a length-prefixed digest, then the record.
pub fn table_root(table_item: &[u8]) -> Result<Digest, WalkError> {
    if table_item.len() < 40 || u64::from_le_bytes(table_item[..8].try_into().expect("8")) != 32 {
        return Err(WalkError::FirstQuery(
            "the table item does not begin with a 32-byte commitment".into(),
        ));
    }
    Ok(table_item[8..40].try_into().expect("32"))
}

/// The trusted inputs of one chain's walk.
pub struct ChainInputs<'a> {
    pub label: u64,
    pub plan: &'a Parameters,
    pub parameters_digest: Digest,
    pub statement: &'a [u8],
    pub configuration: Digest,
    pub schedule: &'a OpeningSchedule,
    /// `None`: the chain's 32 random bytes are the first bytes of its part of the proof.
    /// `Some(d)`: both sides take them from a bound value (R4.5).
    pub given_salt: Option<Digest>,
    /// The root of the committed table named in this chain's statement, if any.
    pub table_root: Option<Digest>,
    /// Chains this one follows: their seals are items of this statement.
    pub follows: &'a [&'a ChainWalk],
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
pub fn walk_first_chain(
    proof: &[u8],
    inputs: &ChainInputs<'_>,
    session: &mut Session,
) -> Result<ChainWalk, WalkError> {
    let (_, salt) = read_head(proof)?;
    let i = ChainInputs {
        given_salt: Some(salt),
        ..*inputs
    };
    let mut w = walk_chain(proof, PROOF_HEAD_BYTES, &i, session)?;
    w.salt_in_proof = true; // read by read_head, the head's last 32 bytes
    w.start = 12;
    Ok(w)
}

/// Walks one chain from `start`. `session` holds the vertex records of every
/// root seen so far in this verdict (R7.14).
pub fn walk_chain(
    proof: &[u8],
    start: usize,
    inputs: &ChainInputs<'_>,
    session: &mut Session,
) -> Result<ChainWalk, WalkError> {
    let label = inputs.label;
    let plan = inputs.plan;
    let tr = |round: u64| {
        move |error: TranscriptError| WalkError::Transcript {
            chain: label,
            round,
            error,
        }
    };
    let mut cur = Cursor {
        b: proof,
        at: start,
    };
    let salt = match inputs.given_salt {
        Some(s) => s,
        None => cur.digest(&format!("chain {label:x}: random bytes"))?,
    };
    let run = run_value(label, &inputs.parameters_digest, &salt).map_err(tr(0))?;
    let rho0 = first_value(
        label,
        &inputs.parameters_digest,
        inputs.statement,
        Some(&run),
    )
    .map_err(tr(0))?;
    let salt_bytes =
        usize::try_from(plan.salt_bytes).map_err(|_| WalkError::Plan("salt".into()))?;
    let nonce_bytes =
        usize::try_from(plan.nonce_bytes).map_err(|_| WalkError::Plan("nonce".into()))?;
    if !(1..=8).contains(&nonce_bytes) || plan.position_bytes != 0 {
        return Err(WalkError::Plan(
            "a nonce has 1 to 8 bytes, and a proof lists no position".into(),
        ));
    }
    let expanded = expand(&plan.rounds)?;
    for (k, _) in inputs.schedule.for_chain(label) {
        let e = usize::try_from(*k)
            .ok()
            .and_then(|k| k.checked_sub(1))
            .and_then(|i| expanded.get(i));
        match e {
            Some(e) if kind_of_name(&e.name)? == RoundKind::Positions => {}
            _ => {
                return Err(WalkError::Schedule(format!(
                    "chain {label:x}: round {k} is no positions round of its plan"
                )))
            }
        }
    }

    let mut chain = Chain::new(label, rho0).map_err(tr(0))?;
    let mut rounds = Vec::with_capacity(expanded.len());
    let mut openings = Vec::new();
    let mut roots: Vec<Digest> = Vec::new();
    let mut seal = None;
    let mut round_draws: Vec<Draw> = Vec::with_capacity(expanded.len());

    for (i, entry) in expanded.iter().enumerate() {
        let rno = i as u64 + 1;
        let kind = kind_of_name(&entry.name)?;
        if seal.is_some() {
            return Err(WalkError::Plan(format!(
                "chain {label:x}: a round after its seal"
            )));
        }
        let mlen = usize::try_from(entry.message_bytes).map_err(|_| WalkError::TooLarge)?;
        let moff = cur.at;
        let message = cur.take(mlen, || format!("chain {label:x} round {rno} message"))?;
        if entry.roots > 0 {
            // R8.3: the answers to out-of-domain samples come first (24 bytes each);
            // then the roots, in the order of their trees' numbers (R8.6); in a
            // kind-2 round the hiding sum is the last item (R8.4). The rest of a
            // message's item list is protocol data (R8.8, stage D9). A root read
            // from the wrong bytes cannot pass: every opening is checked against it.
            let at = entry.answers.checked_mul(24).ok_or(WalkError::TooLarge)?;
            let end = entry
                .roots
                .checked_mul(32)
                .and_then(|r| r.checked_add(at))
                .ok_or(WalkError::TooLarge)?;
            let tail = if kind == RoundKind::Epsilon { 24 } else { 0 };
            if end.checked_add(tail).ok_or(WalkError::TooLarge)? > entry.message_bytes {
                return Err(WalkError::RootLayout {
                    chain: label,
                    round: rno,
                    message_bytes: entry.message_bytes,
                    roots: entry.roots,
                });
            }
            for c in message[at as usize..end as usize].chunks_exact(32) {
                roots.push(c.try_into().expect("32 bytes"));
            }
        }
        let work = u8::try_from(entry.work).map_err(|_| WalkError::Plan("work bits".into()))?;
        let (nonce, noff) = if work > 0 {
            let at = cur.at;
            let raw = cur.take(nonce_bytes, || format!("chain {label:x} round {rno} nonce"))?;
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
        if kind == RoundKind::Seal {
            seal = Some(draw.seal().map_err(tr(rno))?);
            round_draws.push(draw);
            continue;
        }

        let Some(scheduled) = inputs.schedule.by_round.get(&(label, rno)) else {
            if kind == RoundKind::Positions {
                return Err(WalkError::Schedule(format!(
                    "chain {label:x}: positions round {rno} ({}) has no scheduled opening",
                    entry.name
                )));
            }
            round_draws.push(draw);
            continue;
        };
        // R6.10: the positions come first in a kind-4 round's draw.
        let log_n = u32::try_from(entry.log_n).map_err(|_| WalkError::Plan("log_n".into()))?;
        let width = u8::try_from(entry.log_n).map_err(|_| WalkError::Plan("log_n".into()))?;
        if entry.positions == 0 || entry.positions > 1 << 20 {
            return Err(WalkError::Plan(format!(
                "chain {label:x} round {rno}: draw_positions"
            )));
        }
        let mut draws = Vec::with_capacity(entry.positions as usize);
        for _ in 0..entry.positions {
            draws.push(draw.position(width).map_err(tr(rno))?);
        }
        let list =
            PositionList::from_draws(draws, log_n).map_err(|error| WalkError::Positions {
                chain: label,
                round: rno,
                error,
            })?;
        for s in scheduled {
            let at = cur.at;
            let err = |error| WalkError::Opening {
                chain: label,
                round: rno,
                tree: s.tree,
                offset: at,
                error,
            };
            let (root, tree_run, stored, salt) = match s.root {
                RootSource::Table => (
                    inputs.table_root.ok_or(WalkError::NoRoot {
                        chain: label,
                        round: rno,
                        tree: s.tree,
                    })?,
                    run,
                    true,
                    s.salt.unwrap_or(0),
                ),
                RootSource::Received { chain: c, index } if c == label => (
                    *roots.get(index).ok_or(WalkError::NoRoot {
                        chain: label,
                        round: rno,
                        tree: s.tree,
                    })?,
                    run,
                    false,
                    salt_bytes,
                ),
                RootSource::Received { chain: c, index } => {
                    let earlier = inputs
                        .follows
                        .iter()
                        .find(|w| w.label == c)
                        .ok_or_else(|| WalkError::Linkage(format!("chain {label:x} opens a tree of chain {c:x}, which it does not follow")))?;
                    let r = *earlier.roots.get(index).ok_or(WalkError::NoRoot {
                        chain: label,
                        round: rno,
                        tree: s.tree,
                    })?;
                    (r, earlier.run, false, salt_bytes)
                }
            };
            let shape = OracleTreeShape {
                log_n: s.log_n,
                log_n_zk: s.log_n_zk,
                main_symbols: s.main_symbols.clone(),
                mask_symbols: s.mask_symbols.clone(),
                tree_number: s.tree,
                salt_bytes: salt,
                stored,
                run: tree_run,
                parameters: inputs.configuration,
            };
            if s.log_n > log_n {
                return Err(err(MerkleError::InvalidList(
                    "tree deeper than its list's range",
                )));
            }
            let own = list.for_tree(s.log_n).map_err(err)?;
            let need = opening_bytes(&shape, &own).map_err(err)?;
            let (opened, used) =
                receive_opening(&proof[at..], &root, &shape, &own, session).map_err(err)?;
            debug_assert_eq!(used, need);
            cur.at += used;
            openings.push(OpeningRecord {
                chain: label,
                after_round: rno,
                tree: s.tree,
                stored,
                offset: at,
                bytes: used,
                root,
                list: own.all().to_vec(),
                draws: own.draws().len(),
                run: if stored { [0; 32] } else { tree_run },
                parameters: inputs.configuration,
                given: tree_given_count(s.log_n, &own).map_err(err)?,
                salt_bytes: salt,
                draw_list: own.draws().to_vec(),
                width: opened.width(),
                columns: opened.columns,
            });
        }
        round_draws.push(draw);
    }
    if round_draws.len() != rounds.len() {
        return Err(WalkError::Plan(format!(
            "chain {label:x}: internal: {} draws for {} rounds",
            round_draws.len(),
            rounds.len()
        )));
    }
    Ok(ChainWalk {
        label,
        start,
        salt_in_proof: inputs.given_salt.is_none(),
        run,
        configuration: inputs.configuration,
        rho0,
        rounds,
        openings,
        roots,
        seal,
        end: cur.at,
        draws: round_draws,
    })
}

/// The binding tree's shape, from the first chain's parameter `binding tree`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BindingShape {
    pub log_leaves: u32,
    pub salt_bytes: usize,
}
impl BindingShape {
    pub fn from_item(v: &[u8]) -> Result<Self, WalkError> {
        if v.len() != 16 {
            return Err(WalkError::FirstQuery("binding tree: two words".into()));
        }
        let l = u64::from_le_bytes(v[..8].try_into().expect("8"));
        let s = u64::from_le_bytes(v[8..].try_into().expect("8"));
        if l > 48 || !flashprove_merkle::salt_length_fits(s as usize) {
            return Err(WalkError::FirstQuery(
                "binding tree: depth above 48 or salt length".into(),
            ));
        }
        Ok(Self {
            log_leaves: l as u32,
            salt_bytes: s as usize,
        })
    }
}

/// The place (R7.18): the request's place, its leaf's salt, the siblings
/// upward. Returns the binding root and the bytes read.
pub fn binding_root(
    bytes: &[u8],
    shape: BindingShape,
    configuration: &Digest,
    seal: &Digest,
) -> Result<(Digest, u64, usize), WalkError> {
    let mut cur = Cursor { b: bytes, at: 0 };
    let place = u64::from_le_bytes(cur.take(8, || "place".into())?.try_into().expect("8"));
    if (place >> shape.log_leaves) != 0 {
        return Err(WalkError::Place(format!(
            "place {place} outside 2^{}",
            shape.log_leaves
        )));
    }
    let salt = cur.take(shape.salt_bytes, || "place: salt".into())?;
    let hash = |e: TranscriptError| WalkError::Place(e.to_string());
    let at = leaf_salt_at(4, shape.salt_bytes).map_err(|e| WalkError::Place(e.to_string()))?;
    let mut leaf = seal.to_vec();
    leaf.resize(at - 16, 0);
    leaf.extend_from_slice(salt);
    let mut node: Digest = h(
        LEAF_BINDING,
        0,
        (1_u64 << shape.log_leaves) + place,
        Some(configuration),
        &leaf,
        Some((4, (shape.salt_bytes / 8) as u8)),
    )
    .map_err(hash)?
    .try_into()
    .expect("32");
    let mut p = place;
    for _ in 0..shape.log_leaves {
        let sib = cur.digest("place: sibling")?;
        let mut b = [0_u8; 64];
        if p & 1 == 1 {
            b[..32].copy_from_slice(&sib);
            b[32..].copy_from_slice(&node);
        } else {
            b[..32].copy_from_slice(&node);
            b[32..].copy_from_slice(&sib);
        }
        node = h(BINDING_NODE, 0, 0, Some(configuration), &b, None)
            .map_err(hash)?
            .try_into()
            .expect("32");
        p >>= 1;
    }
    Ok((node, place, cur.at))
}

/// One chain's serialized first query (parameters and statement), as the
/// reference's Binder writes them. Stage D7 derives these natively.
pub struct FirstQueryBytes<'a> {
    pub parameters: &'a [u8],
    pub statement: &'a [u8],
}
pub struct ProofInputs<'a> {
    pub policy: &'a [u8],
    pub layout: &'a [u8],
    pub scales: &'a [u8],
    pub request: &'a [u8],
    pub first: FirstQueryBytes<'a>,
    pub shared: FirstQueryBytes<'a>,
    pub second: FirstQueryBytes<'a>,
    pub schedule: &'a OpeningSchedule,
}
#[derive(Debug, Clone)]
pub struct ProofWalk {
    pub configuration: Digest,
    pub copy: u32,
    pub chains: Vec<ChainWalk>,
    pub place: u64,
    pub place_span: (usize, usize),
    pub binding_root: Digest,
    pub table_root: Digest,
    pub merkle_vertices: usize,
}

fn query_err(what: &str) -> impl Fn(QueryError) -> WalkError + '_ {
    move |e| WalkError::FirstQuery(format!("{what}: {e}"))
}
fn names(items: &[Item]) -> Vec<&str> {
    items.iter().map(|i| i.name.as_str()).collect()
}

/// Walks the whole proof file to its last byte (R14.3: head | first chain |
/// place | shared chain | second chain), checking every first query's items
/// against what the walk computes and every opening against its root.
pub fn walk_proof(proof: &[u8], i: &ProofInputs<'_>) -> Result<ProofWalk, WalkError> {
    let (copy, _) = read_head(proof)?;
    let configuration = configuration_digest(&[i.policy, i.layout, i.scales])
        .map_err(|e| WalkError::FirstQuery(e.to_string()))?;
    let mut session = Session::default();

    // First chain: audited against the public files as before.
    let p1 = flashprove_transcript::first_query::audit(
        i.first.parameters,
        i.first.statement,
        [i.policy, i.layout, i.scales],
        i.request,
        copy,
    )
    .map_err(query_err("first chain"))?;
    let s1 = parse_items(i.first.statement)?;
    let table_item = item(&s1, "table")?.to_vec();
    let table = table_root(&table_item)?;
    let binding = BindingShape::from_item(item(&p1.items, "binding tree")?)?;
    let pd1 = parameters_digest(i.first.parameters).map_err(query_err("first chain"))?;
    let c1 = walk_first_chain(
        proof,
        &ChainInputs {
            label: LABEL_FIRST_CHAIN,
            plan: &p1,
            parameters_digest: pd1,
            statement: i.first.statement,
            configuration,
            schedule: i.schedule,
            given_salt: None,
            table_root: Some(table),
            follows: &[],
        },
        &mut session,
    )?;
    let seal1 = c1.seal.ok_or(WalkError::NoSeal(LABEL_FIRST_CHAIN))?;

    // The place: the first chain's seal up the binding tree.
    let (broot, place, used) = binding_root(&proof[c1.end..], binding, &configuration, &seal1)?;
    let place_span = (c1.end, c1.end + used);

    // Shared chain: parameters are the first chain's LIN parameters; statement
    // is the table and the binding root, which is also its salt.
    let p3 = parse_parameters(i.shared.parameters).map_err(query_err("shared chain"))?;
    if names(&p3.items) != ["configuration", "codes", "the test on the table"] {
        return Err(WalkError::Linkage(format!(
            "shared chain parameters: {:?}",
            names(&p3.items)
        )));
    }
    if item(&p3.items, "configuration")? != configuration {
        return Err(WalkError::Linkage(
            "shared chain: another configuration".into(),
        ));
    }
    for n in ["codes", "the test on the table"] {
        if item(&p3.items, n)? != item(&p1.items, n)? {
            return Err(WalkError::Linkage(format!(
                "shared chain: '{n}' differs from the first chain's"
            )));
        }
    }
    let s3 = parse_items(i.shared.statement)?;
    if names(&s3) != ["table", "the binding tree's root"] {
        return Err(WalkError::Linkage(format!(
            "shared chain statement: {:?}",
            names(&s3)
        )));
    }
    if item(&s3, "table")? != table_item {
        return Err(WalkError::Linkage(
            "shared chain: another table than the first chain's".into(),
        ));
    }
    if item(&s3, "the binding tree's root")? != broot {
        return Err(WalkError::Linkage(
            "shared chain: the binding root differs from the one this walk computed from the place"
                .into(),
        ));
    }
    let pd3 = parameters_digest(i.shared.parameters).map_err(query_err("shared chain"))?;
    let c3 = walk_chain(
        proof,
        place_span.1,
        &ChainInputs {
            label: LABEL_PROOF_SHARED_CHAIN,
            plan: &p3,
            parameters_digest: pd3,
            statement: i.shared.statement,
            configuration,
            schedule: i.schedule,
            given_salt: Some(broot),
            table_root: Some(table),
            follows: &[],
        },
        &mut session,
    )?;
    let seal3 = c3.seal.ok_or(WalkError::NoSeal(LABEL_PROOF_SHARED_CHAIN))?;

    // Second chain: follows the first chain and the shared chain.
    let p4 = parse_parameters(i.second.parameters).map_err(query_err("second chain"))?;
    if names(&p4.items) != ["configuration"] || item(&p4.items, "configuration")? != configuration {
        return Err(WalkError::Linkage(
            "second chain parameters: exactly the configuration".into(),
        ));
    }
    let s4 = parse_items(i.second.statement)?;
    if names(&s4) != [SEAL_ITEM, SEAL_ITEM] || s4[0].value != seal1 || s4[1].value != seal3 {
        return Err(WalkError::Linkage(
            "second chain statement: exactly the first chain's seal, then the shared chain's"
                .into(),
        ));
    }
    let pd4 = parameters_digest(i.second.parameters).map_err(query_err("second chain"))?;
    let follows = [&c1, &c3];
    let c4 = walk_chain(
        proof,
        c3.end,
        &ChainInputs {
            label: LABEL_PROOF_SECOND_CHAIN,
            plan: &p4,
            parameters_digest: pd4,
            statement: i.second.statement,
            configuration,
            schedule: i.schedule,
            given_salt: None,
            table_root: None,
            follows: &follows,
        },
        &mut session,
    )?;
    if c4.end != proof.len() {
        return Err(WalkError::LeftOver {
            at: c4.end,
            len: proof.len(),
        });
    }
    // Every scheduled opening belongs to one of the three chains.
    let known = [
        LABEL_FIRST_CHAIN,
        LABEL_PROOF_SHARED_CHAIN,
        LABEL_PROOF_SECOND_CHAIN,
    ];
    if let Some(((c, _), _)) = i
        .schedule
        .by_round
        .iter()
        .find(|((c, _), _)| !known.contains(c))
    {
        return Err(WalkError::Schedule(format!(
            "an opening scheduled for chain {c:x}, which is not in a proof file"
        )));
    }
    let mut all_roots: Vec<Digest> = [&c1, &c3, &c4]
        .iter()
        .flat_map(|c| c.roots.iter().copied())
        .collect();
    all_roots.push(table);
    all_roots.sort_unstable();
    all_roots.dedup();
    let merkle_vertices = all_roots.iter().map(|r| session.record(r).vertices()).sum();
    Ok(ProofWalk {
        configuration,
        copy,
        chains: vec![c1, c3, c4],
        place,
        place_span,
        binding_root: broot,
        table_root: table,
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
        let ok = "chain=46524d01 after_round=5 tree=0 root=46524d01:0 log_n=3 log_n_zk=0 main=2 mask=0\n# c\n\
                  chain=46524d03 after_round=4 tree=0 root=table log_n=3 log_n_zk=0 main=2 mask=0 salt=40\n";
        let s = OpeningSchedule::parse(ok).unwrap();
        assert_eq!(s.len(), 2);
        assert_eq!(s.by_round[&(0x46524d03, 4)][0].root, RootSource::Table);
        for bad in [
            "chain=46524d01 after_round=5 tree=0 root=46524d01:0 log_n=3 log_n_zk=0 main=2",
            "chain=46524d01 after_round=5 tree=0 root=46524d01:0 log_n=3 log_n_zk=0 main=2 mask=0 extra=1",
            "chain=46524d01 after_round=5 tree=0 root=46524d01:0 log_n=3 log_n_zk=0 main=2 mask=0\n\
             chain=46524d01 after_round=5 tree=0 root=46524d01:0 log_n=3 log_n_zk=0 main=2 mask=0",
            "chain=46524d01 after_round=x tree=0 root=46524d01:0 log_n=3 log_n_zk=0 main=2 mask=0",
            "chain=46524d01 after_round=5 tree=0 root=table log_n=3 log_n_zk=0 main=2 mask=0",
            "chain=46524d01 after_round=5 tree=0 root=46524d01:0 log_n=3 log_n_zk=0 main=2 mask=0 salt=40",
            "chain=46524d01 after_round=5 tree=0 root=0 log_n=3 log_n_zk=0 main=2 mask=0",
        ] {
            assert!(OpeningSchedule::parse(bad).is_err(), "{bad}");
        }
    }

    #[test]
    fn items_and_table_root() {
        let mut b = Vec::new();
        for (n, v) in [
            (
                "table",
                [&32_u64.to_le_bytes()[..], &[7; 32], &[1, 2, 3]].concat(),
            ),
            ("x", vec![]),
        ] {
            b.extend_from_slice(&(n.len() as u64).to_le_bytes());
            b.extend_from_slice(n.as_bytes());
            b.extend_from_slice(&(v.len() as u64).to_le_bytes());
            b.extend_from_slice(&v);
        }
        let it = parse_items(&b).unwrap();
        assert_eq!(names(&it), ["table", "x"]);
        assert_eq!(table_root(item(&it, "table").unwrap()).unwrap(), [7; 32]);
        assert!(parse_items(&b[..b.len() - 1]).is_err());
        assert!(table_root(&[0; 39]).is_err());
    }

    #[test]
    fn binding_path_round_trip() {
        // A depth-2 binding tree built here; the path of place 2 leads to its root.
        let cfg = [9_u8; 32];
        let shape = BindingShape {
            log_leaves: 2,
            salt_bytes: 40,
        };
        let leaf = |place: u64, seal: &Digest, salt: &[u8]| -> Digest {
            let mut b = seal.to_vec();
            b.extend_from_slice(salt);
            h(LEAF_BINDING, 0, 4 + place, Some(&cfg), &b, Some((4, 5)))
                .unwrap()
                .try_into()
                .unwrap()
        };
        let node = |l: &Digest, r: &Digest| -> Digest {
            h(
                BINDING_NODE,
                0,
                0,
                Some(&cfg),
                &[&l[..], &r[..]].concat(),
                None,
            )
            .unwrap()
            .try_into()
            .unwrap()
        };
        let seals: Vec<Digest> = (0..4).map(|i| [i as u8 + 1; 32]).collect();
        let salts: Vec<Vec<u8>> = (0..4).map(|i| vec![i as u8 + 50; 40]).collect();
        let l: Vec<Digest> = (0..4)
            .map(|p| leaf(p, &seals[p as usize], &salts[p as usize]))
            .collect();
        let (a, b) = (node(&l[0], &l[1]), node(&l[2], &l[3]));
        let root = node(&a, &b);
        let mut path = 2_u64.to_le_bytes().to_vec();
        path.extend_from_slice(&salts[2]);
        path.extend_from_slice(&l[3]);
        path.extend_from_slice(&a);
        let (r, place, used) = binding_root(&path, shape, &cfg, &seals[2]).unwrap();
        assert_eq!((r, place, used), (root, 2, path.len()));
        assert_ne!(binding_root(&path, shape, &cfg, &seals[1]).unwrap().0, root);
        let mut bad = path.clone();
        bad[0] = 4;
        assert!(binding_root(&bad, shape, &cfg, &seals[2]).is_err());
        assert!(binding_root(&path[..path.len() - 1], shape, &cfg, &seals[2]).is_err());
    }
}
