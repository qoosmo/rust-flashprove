//! H821 Merkle openings of oracle trees.
//!
//! Grounded in upstream FORMAT.md R7.1-R7.16 and in `blocks/tree/opening.h`,
//! `blocks/tree/tree.h`, `blocks/tree/positions.h` at the pinned revision.
//!
//! Trust boundary: every field of an [`OracleTreeShape`] and every
//! [`PositionList`] must come from the verifier's own plan, configuration and
//! Fiat-Shamir draws, never from proof bytes. [`read_opening`] takes no index,
//! count or direction from the proof; [`check_opening`] accepts only if the walk
//! uses exactly the given digests, ends in the expected root, and no vertex gets
//! two values under one root (R7.14).
//!
//! What an accepted opening shows: the opened columns are the leaves of the
//! committed tree at those positions. It does NOT show that the columns satisfy
//! any algebraic relation; that is the job of the protocol checks (stage D9).

use flashprove_field::Fp;
use flashprove_transcript::{h, Digest};
use std::collections::{BTreeMap, HashMap};
use std::fmt;

/// Domain numbers (upstream `blocks/hash/domains.h`).
pub const LEAF_MAIN: u16 = 164;
pub const TREE_NODE: u16 = 166;
pub const LEAF_STORED_MAIN: u16 = 174;

pub const F_BYTES: usize = 8;
pub const DIGEST_BYTES: usize = 32;
pub const SALT_FLOOR_BYTES: usize = 40;
pub const SALT_MOST_BYTES: usize = 64;
/// R7.16.
pub const MAX_LOG_N: u32 = 48;
/// The leaf tag holds the width in 24 bits.
pub const MAX_WIDTH: usize = (1 << 24) - 1;
const LABEL_BYTES: usize = 16;
const BLOCK_BYTES: usize = 128;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MerkleError {
    /// A shape that no plan of the format can have.
    InvalidShape(&'static str),
    /// A list that does not fit the shape (empty, another range, unsorted).
    InvalidList(&'static str),
    /// Arithmetic on sizes overflowed.
    Overflow,
    /// The proof ends before the opening's last byte.
    Truncated { needed: usize, left: usize },
    /// A symbol at or above the modulus (R1.3).
    NonCanonical {
        column: usize,
        symbol: usize,
        value: u64,
    },
    /// The walk ran out of given digests (cannot happen after a successful read).
    MissingGiven,
    /// The walk did not use every given digest.
    UnusedGiven,
    /// The walk did not end in the expected root.
    WrongRoot,
    /// A vertex got a second, different value under one root (R7.14).
    Clash,
    /// Hash precondition rejected by the transcript primitive.
    Hash(String),
}
impl fmt::Display for MerkleError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for MerkleError {}

/// R7.2: the short position of x among rows of length 2^log_short.
pub fn short_position(log_n: u32, log_short: u32, x: u64) -> Result<u64, MerkleError> {
    if log_short > log_n || log_n >= 64 || (x >> log_n) != 0 {
        return Err(MerkleError::InvalidList("short position outside its range"));
    }
    Ok(x & ((1_u64 << log_short) - 1))
}

/// The positions at which a tree is opened (upstream `PositionList`).
/// Built only from the verifier's draws: sorted, without duplicates; the
/// draws are kept, repeats included, in the order drawn.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PositionList {
    x: Vec<u64>,
    draws: Vec<u64>,
    log_n: u32,
}
impl PositionList {
    pub fn from_draws(draws: Vec<u64>, log_n: u32) -> Result<Self, MerkleError> {
        if log_n >= 64 {
            return Err(MerkleError::InvalidList("range 2^k needs k below 64"));
        }
        if draws.is_empty() {
            return Err(MerkleError::InvalidList("a list needs at least one draw"));
        }
        if draws.iter().any(|&d| (d >> log_n) != 0) {
            return Err(MerkleError::InvalidList("a draw outside the range"));
        }
        let mut x = draws.clone();
        x.sort_unstable();
        x.dedup();
        Ok(Self { x, draws, log_n })
    }
    pub fn log_n(&self) -> u32 {
        self.log_n
    }
    pub fn len(&self) -> usize {
        self.x.len()
    }
    pub fn is_empty(&self) -> bool {
        self.x.is_empty()
    }
    pub fn all(&self) -> &[u64] {
        &self.x
    }
    pub fn draws(&self) -> &[u64] {
        &self.draws
    }
    /// R7.15: the list for a tree over rows of length 2^log_short.
    pub fn short_list(&self, log_short: u32) -> Result<Self, MerkleError> {
        let y = self
            .draws
            .iter()
            .map(|&d| short_position(self.log_n, log_short, d))
            .collect::<Result<Vec<_>, _>>()?;
        Self::from_draws(y, log_short)
    }
    /// Draws first..first+count only (a verifier message may hold several lists).
    pub fn part(&self, first: usize, count: usize) -> Result<Self, MerkleError> {
        let end = first.checked_add(count).ok_or(MerkleError::Overflow)?;
        if count == 0 || end > self.draws.len() {
            return Err(MerkleError::InvalidList("a part beyond the list's draws"));
        }
        Self::from_draws(self.draws[first..end].to_vec(), self.log_n)
    }
    /// The list for a tree of depth `log_n`: this list, or its short list.
    pub fn for_tree(&self, log_n: u32) -> Result<Self, MerkleError> {
        if log_n == self.log_n {
            Ok(self.clone())
        } else {
            self.short_list(log_n)
        }
    }
}

/// Upstream `OracleTreeShape`. Every field comes from the verifier's plan,
/// configuration and channel; `stored` least of all may come from a proof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OracleTreeShape {
    pub log_n: u32,
    pub log_n_zk: u32,
    /// Elements of F that each part has in a column, of its main rows.
    pub main_symbols: Vec<usize>,
    /// Elements of F that each part has in a column, of its mask rows.
    pub mask_symbols: Vec<usize>,
    pub tree_number: u32,
    pub salt_bytes: usize,
    pub stored: bool,
    /// Rounds::run() of the chain that sent the root (unused if stored).
    pub run: Digest,
    /// The configuration digest; start of every inner vertex hash.
    pub parameters: Digest,
}
fn sum(v: &[usize]) -> Result<usize, MerkleError> {
    v.iter()
        .try_fold(0_usize, |a, &b| a.checked_add(b))
        .ok_or(MerkleError::Overflow)
}
pub fn salt_length_fits(s: usize) -> bool {
    (SALT_FLOOR_BYTES..=SALT_MOST_BYTES).contains(&s) && s % 8 == 0
}
impl OracleTreeShape {
    pub fn main_width(&self) -> Result<usize, MerkleError> {
        sum(&self.main_symbols)
    }
    pub fn mask_width(&self) -> Result<usize, MerkleError> {
        sum(&self.mask_symbols)
    }
    pub fn width(&self) -> Result<usize, MerkleError> {
        self.main_width()?
            .checked_add(self.mask_width()?)
            .ok_or(MerkleError::Overflow)
    }
    /// Mirrors `OracleTreeShape::valid()`, plus R7.4's tree number 0 for stored trees.
    pub fn validate(&self) -> Result<(), MerkleError> {
        if self.main_symbols.len() != self.mask_symbols.len() {
            return Err(MerkleError::InvalidShape(
                "an entry of each width for every part",
            ));
        }
        let (main, mask) = (self.main_width()?, self.mask_width()?);
        if main == 0 && mask == 0 {
            return Err(MerkleError::InvalidShape("a tree without rows"));
        }
        if mask > 0 && self.log_n_zk > self.log_n {
            return Err(MerkleError::InvalidShape(
                "mask rows longer than the main rows",
            ));
        }
        if main == 0 && self.log_n != self.log_n_zk {
            return Err(MerkleError::InvalidShape(
                "a tree of mask rows only has log_n == log_n_zk",
            ));
        }
        if !salt_length_fits(self.salt_bytes) {
            return Err(MerkleError::InvalidShape("salt length"));
        }
        if self.width()? > MAX_WIDTH {
            return Err(MerkleError::InvalidShape(
                "column too wide for the leaf tag",
            ));
        }
        if self.parameters == [0; 32] || (!self.stored && self.run == [0; 32]) {
            return Err(MerkleError::InvalidShape("a hash start left unset"));
        }
        if self.tree_number >= 1 << 16 {
            return Err(MerkleError::InvalidShape("tree number of 2^16 or more"));
        }
        if self.stored && self.tree_number != 0 {
            return Err(MerkleError::InvalidShape(
                "a stored tree has tree number 0 (R7.4)",
            ));
        }
        if self.log_n > MAX_LOG_N {
            return Err(MerkleError::InvalidShape("depth above 48"));
        }
        Ok(())
    }
    fn fits(&self, list: &PositionList) -> Result<(), MerkleError> {
        self.validate()?;
        if list.is_empty() || list.log_n() != self.log_n {
            return Err(MerkleError::InvalidList(
                "the list does not range over the tree's positions",
            ));
        }
        Ok(())
    }
}

/// R7.9: the walk from the opened leaves to the root, shared by every use.
trait Side {
    type Value: Clone;
    fn leaf(&mut self, i: usize) -> Self::Value;
    fn given(&mut self, depth: u32, place: u64) -> Option<Self::Value>;
    fn node(
        &mut self,
        depth: u32,
        place: u64,
        left: &Self::Value,
        right: &Self::Value,
    ) -> Result<Self::Value, MerkleError>;
}
fn tree_walk<S: Side>(
    log_n: u32,
    list: &PositionList,
    side: &mut S,
) -> Result<Option<S::Value>, MerkleError> {
    if log_n > MAX_LOG_N || list.is_empty() || list.log_n() != log_n {
        return Err(MerkleError::InvalidList(
            "walk over a list that does not fit the tree",
        ));
    }
    let mut now: Vec<(u64, S::Value)> = list
        .all()
        .iter()
        .enumerate()
        .map(|(i, &x)| (x, side.leaf(i)))
        .collect();
    let mut next = Vec::with_capacity(now.len());
    for d in (1..=log_n).rev() {
        next.clear();
        let mut v = 0;
        while v < now.len() {
            let place = now[v].0;
            let parent = place >> 1;
            if place & 1 == 0 && v + 1 < now.len() && now[v + 1].0 == place + 1 {
                let value = side.node(d - 1, parent, &now[v].1, &now[v + 1].1)?;
                next.push((parent, value));
                v += 2;
            } else {
                let Some(other) = side.given(d, place ^ 1) else {
                    return Ok(None);
                };
                let value = if place & 1 == 1 {
                    side.node(d - 1, parent, &other, &now[v].1)?
                } else {
                    side.node(d - 1, parent, &now[v].1, &other)?
                };
                next.push((parent, value));
                v += 1;
            }
        }
        std::mem::swap(&mut now, &mut next);
    }
    if now.len() != 1 {
        return Err(MerkleError::InvalidList("walk did not end in one vertex"));
    }
    Ok(Some(now.swap_remove(0).1))
}

/// The number of given digests in an opening at `list` of a tree of depth `log_n`.
pub fn tree_given_count(log_n: u32, list: &PositionList) -> Result<usize, MerkleError> {
    struct Count(usize);
    impl Side for Count {
        type Value = ();
        fn leaf(&mut self, _: usize) {}
        fn given(&mut self, _: u32, _: u64) -> Option<()> {
            self.0 += 1;
            Some(())
        }
        fn node(&mut self, _: u32, _: u64, _: &(), _: &()) -> Result<(), MerkleError> {
            Ok(())
        }
    }
    let mut c = Count(0);
    tree_walk(log_n, list, &mut c)?;
    Ok(c.0)
}

/// R7.8: m (8 W + s) + 32 g bytes.
pub fn opening_bytes(shape: &OracleTreeShape, list: &PositionList) -> Result<usize, MerkleError> {
    shape.fits(list)?;
    let per_leaf = shape
        .width()?
        .checked_mul(F_BYTES)
        .and_then(|b| b.checked_add(shape.salt_bytes))
        .ok_or(MerkleError::Overflow)?;
    let leaves = list
        .len()
        .checked_mul(per_leaf)
        .ok_or(MerkleError::Overflow)?;
    let given = tree_given_count(shape.log_n, list)?
        .checked_mul(DIGEST_BYTES)
        .ok_or(MerkleError::Overflow)?;
    leaves.checked_add(given).ok_or(MerkleError::Overflow)
}

/// A decoded opening. Columns are canonical field elements, in list order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Opening {
    pub columns: Vec<Fp>,
    pub salts: Vec<u8>,
    pub given: Vec<Digest>,
    pub main_width: usize,
    pub mask_width: usize,
}
impl Opening {
    pub fn width(&self) -> usize {
        self.main_width + self.mask_width
    }
    pub fn column(&self, i: usize) -> &[Fp] {
        let w = self.width();
        &self.columns[i * w..(i + 1) * w]
    }
    pub fn main_column(&self, i: usize) -> &[Fp] {
        &self.column(i)[..self.main_width]
    }
    pub fn mask_column(&self, i: usize) -> &[Fp] {
        &self.column(i)[self.main_width..]
    }
}

/// Upstream `read_opening`: reads exactly `opening_bytes(shape, list)` bytes
/// from the front of `bytes`, rejecting a short file and any non-canonical
/// symbol. Returns the opening and the number of bytes consumed. Sizes come
/// from shape and list only.
pub fn read_opening(
    bytes: &[u8],
    shape: &OracleTreeShape,
    list: &PositionList,
) -> Result<(Opening, usize), MerkleError> {
    let need = opening_bytes(shape, list)?;
    if bytes.len() < need {
        return Err(MerkleError::Truncated {
            needed: need,
            left: bytes.len(),
        });
    }
    let w = shape.width()?;
    let g = tree_given_count(shape.log_n, list)?;
    let mut columns = Vec::with_capacity(list.len() * w);
    let mut salts = Vec::with_capacity(list.len() * shape.salt_bytes);
    let mut at = 0;
    for i in 0..list.len() {
        for j in 0..w {
            let word = u64::from_le_bytes(bytes[at..at + 8].try_into().expect("eight bytes"));
            let x = Fp::from_canonical(word).map_err(|_| MerkleError::NonCanonical {
                column: i,
                symbol: j,
                value: word,
            })?;
            columns.push(x);
            at += F_BYTES;
        }
        salts.extend_from_slice(&bytes[at..at + shape.salt_bytes]);
        at += shape.salt_bytes;
    }
    let mut given = Vec::with_capacity(g);
    for _ in 0..g {
        given.push(bytes[at..at + DIGEST_BYTES].try_into().expect("32 bytes"));
        at += DIGEST_BYTES;
    }
    debug_assert_eq!(at, need);
    Ok((
        Opening {
            columns,
            salts,
            given,
            main_width: shape.main_width()?,
            mask_width: shape.mask_width()?,
        },
        need,
    ))
}

/// R7.3: offset of the salt within the hashed string (label included).
pub fn leaf_salt_at(symbols: usize, salt_bytes: usize) -> Result<usize, MerkleError> {
    let content = symbols
        .checked_mul(8)
        .and_then(|b| b.checked_add(LABEL_BYTES))
        .ok_or(MerkleError::Overflow)?;
    if content % BLOCK_BYTES + salt_bytes <= BLOCK_BYTES {
        Ok(content)
    } else {
        (content / BLOCK_BYTES + 1)
            .checked_mul(BLOCK_BYTES)
            .ok_or(MerkleError::Overflow)
    }
}

/// R7.3/R7.4: the digest of the leaf at position x.
pub fn leaf_digest(
    shape: &OracleTreeShape,
    x: u64,
    column: &[Fp],
    salt: &[u8],
) -> Result<Digest, MerkleError> {
    let w = shape.width()?;
    if column.len() != w || salt.len() != shape.salt_bytes || (x >> shape.log_n) != 0 {
        return Err(MerkleError::InvalidShape(
            "a leaf of another shape than its tree",
        ));
    }
    let (number, start) = if shape.stored {
        (LEAF_STORED_MAIN, &shape.parameters)
    } else {
        (LEAF_MAIN, &shape.run)
    };
    let salt_at = leaf_salt_at(w, shape.salt_bytes)?;
    let mut bytes = Vec::with_capacity(salt_at - LABEL_BYTES + salt.len());
    for s in column {
        bytes.extend_from_slice(&s.to_le_bytes());
    }
    bytes.resize(salt_at - LABEL_BYTES, 0); // the fill: hashed, in no file
    bytes.extend_from_slice(salt);
    let index = (1_u64 << shape.log_n) + x;
    let symbols = u32::try_from(w).map_err(|_| MerkleError::Overflow)?;
    let salt_words = u8::try_from(shape.salt_bytes / 8).map_err(|_| MerkleError::Overflow)?;
    let out = h(
        number,
        u64::from(shape.tree_number),
        index,
        Some(start),
        &bytes,
        Some((symbols, salt_words)),
    )
    .map_err(|e| MerkleError::Hash(e.to_string()))?;
    Ok(out.try_into().expect("32-byte digest"))
}

/// R7.7: an inner vertex from its two children.
pub fn vertex(parameters: &Digest, left: &Digest, right: &Digest) -> Result<Digest, MerkleError> {
    let mut bytes = [0_u8; 64];
    bytes[..32].copy_from_slice(left);
    bytes[32..].copy_from_slice(right);
    let out = h(TREE_NODE, 0, 0, Some(parameters), &bytes, None)
        .map_err(|e| MerkleError::Hash(e.to_string()))?;
    Ok(out.try_into().expect("32-byte digest"))
}

/// R7.14: vertex values seen under one root, keyed by 2^depth + place.
/// A rejected opening leaves the record as it was.
#[derive(Debug, Default, Clone)]
pub struct TreeValues {
    seen: BTreeMap<u64, Digest>,
}
impl TreeValues {
    pub fn vertices(&self) -> usize {
        self.seen.len()
    }
}

/// The records of one verification session, one per root (R7.14).
#[derive(Debug, Default, Clone)]
pub struct Session {
    records: HashMap<Digest, TreeValues>,
}
impl Session {
    pub fn record(&mut self, root: &Digest) -> &mut TreeValues {
        self.records.entry(*root).or_default()
    }
    pub fn roots(&self) -> usize {
        self.records.len()
    }
}

/// Upstream `tree_check`: recomputes the root from the opened leaf digests
/// and the given digests; rejects unless every given digest is used, the
/// walk ends in `root`, and (with a record) no vertex clashes.
pub fn tree_check(
    root: &Digest,
    log_n: u32,
    parameters: &Digest,
    list: &PositionList,
    leaves: &[Digest],
    given: &[Digest],
    seen: Option<&mut TreeValues>,
) -> Result<(), MerkleError> {
    if leaves.len() != list.len() {
        return Err(MerkleError::InvalidList(
            "one leaf digest per listed position",
        ));
    }
    struct Check<'a> {
        log_n: u32,
        parameters: &'a Digest,
        list: &'a PositionList,
        leaves: &'a [Digest],
        given: &'a [Digest],
        used: usize,
        noted: Vec<(u64, Digest)>,
    }
    impl Check<'_> {
        fn note(&mut self, d: u32, p: u64, v: Digest) -> Digest {
            if d > 0 {
                self.noted.push(((1_u64 << d) + p, v));
            }
            v
        }
    }
    impl Side for Check<'_> {
        type Value = Digest;
        fn leaf(&mut self, i: usize) -> Digest {
            let (x, v) = (self.list.all()[i], self.leaves[i]);
            self.note(self.log_n, x, v)
        }
        fn given(&mut self, d: u32, p: u64) -> Option<Digest> {
            let v = *self.given.get(self.used)?;
            self.used += 1;
            Some(self.note(d, p, v))
        }
        fn node(&mut self, d: u32, p: u64, l: &Digest, r: &Digest) -> Result<Digest, MerkleError> {
            let v = vertex(self.parameters, l, r)?;
            Ok(self.note(d, p, v))
        }
    }
    let mut side = Check {
        log_n,
        parameters,
        list,
        leaves,
        given,
        used: 0,
        noted: Vec::new(),
    };
    let computed = tree_walk(log_n, list, &mut side)?.ok_or(MerkleError::MissingGiven)?;
    if side.used != given.len() {
        return Err(MerkleError::UnusedGiven);
    }
    if computed != *root {
        return Err(MerkleError::WrongRoot);
    }
    if let Some(seen) = seen {
        // Clash check first, insert only after the whole opening is accepted.
        let mut fresh: BTreeMap<u64, Digest> = BTreeMap::new();
        for (k, v) in &side.noted {
            let prior = seen.seen.get(k).or_else(|| fresh.get(k));
            match prior {
                Some(p) if p != v => return Err(MerkleError::Clash),
                Some(_) => {}
                None => {
                    fresh.insert(*k, *v);
                }
            }
        }
        seen.seen.extend(fresh);
    }
    Ok(())
}

/// Upstream `check_opening`: hashes each opened column with its salt and runs [`tree_check`].
pub fn check_opening(
    root: &Digest,
    shape: &OracleTreeShape,
    list: &PositionList,
    opening: &Opening,
    seen: Option<&mut TreeValues>,
) -> Result<(), MerkleError> {
    shape.fits(list)?;
    let w = shape.width()?;
    if opening.columns.len() != list.len() * w
        || opening.salts.len() != list.len() * shape.salt_bytes
    {
        return Err(MerkleError::InvalidShape(
            "opening sizes differ from shape and list",
        ));
    }
    let mut leaves = Vec::with_capacity(list.len());
    for (i, &x) in list.all().iter().enumerate() {
        let col = &opening.columns[i * w..(i + 1) * w];
        let salt = &opening.salts[i * shape.salt_bytes..(i + 1) * shape.salt_bytes];
        leaves.push(leaf_digest(shape, x, col, salt)?);
    }
    tree_check(
        root,
        shape.log_n,
        &shape.parameters,
        list,
        &leaves,
        &opening.given,
        seen,
    )
}

/// Read and check in one step, against the session's record of `root`.
/// Returns the opening and the bytes consumed.
pub fn receive_opening(
    bytes: &[u8],
    root: &Digest,
    shape: &OracleTreeShape,
    list: &PositionList,
    session: &mut Session,
) -> Result<(Opening, usize), MerkleError> {
    let (o, used) = read_opening(bytes, shape, list)?;
    check_opening(root, shape, list, &o, Some(session.record(root)))?;
    Ok((o, used))
}

/// A prover-side tree, for tests and corpus generation only.
pub mod testing {
    use super::*;

    pub struct Tree {
        pub levels: Vec<Vec<Digest>>,
    }
    impl Tree {
        pub fn build(
            parameters: &Digest,
            log_n: u32,
            leaves: Vec<Digest>,
        ) -> Result<Self, MerkleError> {
            if leaves.len() != 1 << log_n {
                return Err(MerkleError::InvalidShape("2^depth leaves"));
            }
            let mut levels = vec![leaves];
            while levels.last().expect("non-empty").len() > 1 {
                let below = levels.last().expect("non-empty");
                let mut up = Vec::with_capacity(below.len() / 2);
                for pair in below.chunks(2) {
                    up.push(vertex(parameters, &pair[0], &pair[1])?);
                }
                levels.push(up);
            }
            levels.reverse(); // levels[d][place]
            Ok(Self { levels })
        }
        pub fn root(&self) -> Digest {
            self.levels[0][0]
        }
        /// The given digests of an opening, in the walk's order.
        pub fn given(&self, log_n: u32, list: &PositionList) -> Result<Vec<Digest>, MerkleError> {
            struct Fetch<'a>(&'a Tree, Vec<Digest>);
            impl Side for Fetch<'_> {
                type Value = ();
                fn leaf(&mut self, _: usize) {}
                fn given(&mut self, d: u32, p: u64) -> Option<()> {
                    self.1.push(self.0.levels[d as usize][p as usize]);
                    Some(())
                }
                fn node(&mut self, _: u32, _: u64, _: &(), _: &()) -> Result<(), MerkleError> {
                    Ok(())
                }
            }
            let mut f = Fetch(self, Vec::new());
            tree_walk(log_n, list, &mut f)?;
            Ok(f.1)
        }
    }

    /// Visits the given digests' vertex coordinates (depth, place), in order.
    pub fn given_vertices(log_n: u32, list: &PositionList) -> Result<Vec<(u32, u64)>, MerkleError> {
        struct Rec(Vec<(u32, u64)>);
        impl Side for Rec {
            type Value = ();
            fn leaf(&mut self, _: usize) {}
            fn given(&mut self, d: u32, p: u64) -> Option<()> {
                self.0.push((d, p));
                Some(())
            }
            fn node(&mut self, _: u32, _: u64, _: &(), _: &()) -> Result<(), MerkleError> {
                Ok(())
            }
        }
        let mut r = Rec(Vec::new());
        tree_walk(log_n, list, &mut r)?;
        Ok(r.0)
    }
}

#[cfg(test)]
mod tests;
