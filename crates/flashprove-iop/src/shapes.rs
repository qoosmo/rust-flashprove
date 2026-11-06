//! The bound public shapes of LIN and its parts, as they stand in a chain's
//! first query (`public_bytes` in `blocks/iop/lin.h`, `foldeq.h`, `iopp.h`,
//! `context.h`), with the faults the reference checks by themselves.
//!
//! Ported faults: `public_fault(OracleShape)`, `index_fault`,
//! `public_fault(FoldeqShape)`, `public_fault(IoppStage)`, `public_fault(LinShape)`,
//! and of `lin_fault` / `foldeq_fault` / `iopp_fault` the checks that need only
//! the codes. Not yet ported, because they need the SEND pad layout and
//! `vector_lay` (blocks/iop/send.h, foldeq.h): `vector_room` (lin_fault,
//! foldeq_fault) and the stage-to-stage length checks of `iopp_fault`. They are
//! listed in docs/SHARED_CHAIN_MAP.md and land with the SEND port.

use crate::code::{read_code, write_code, Code, Codes, MOST_LOG_N, NONE_ID};
use crate::{put, ParseError, Words};

/// `E_DEGREE`: the cubic extension.
pub const E_DEGREE: u64 = 3;
pub const SALT_FLOOR_BYTES: u64 = 40;
pub const SALT_MOST_BYTES: u64 = 64;

/// `OracleShape` without its print name. `code` is `None` exactly when there
/// are no main rows, `mask_code` exactly when there are no mask rows (the one
/// encoding per shape of `public_bytes(OracleShape)`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OracleShape {
    pub code: Option<u32>,
    pub main_rows: u64,
    pub main_deg: u64,
    pub mask_rows: u64,
    pub mask_code: Option<u32>,
    pub answers: u32,
}
impl OracleShape {
    fn read(w: &mut Words<'_>) -> Result<Self, ParseError> {
        let (code, mask_code, main_rows, main_deg, mask_rows, answers) = (
            w.word()?,
            w.word()?,
            w.word()?,
            w.word()?,
            w.word()?,
            w.u32("answers")?,
        );
        let id = |x: u64, present: bool, what| -> Result<Option<u32>, ParseError> {
            match (present, x == NONE_ID) {
                (false, true) => Ok(None),
                (true, false) => u32::try_from(x)
                    .map(Some)
                    .map_err(|_| ParseError::Overflow(what)),
                _ => Err(ParseError::Fault(
                    "an oracle shape's code is NONE exactly when it has no such rows",
                )),
            }
        };
        if main_rows == 0 && main_deg != 1 {
            return Err(ParseError::Fault(
                "an oracle shape without main rows is written with main_deg 1",
            ));
        }
        let s = Self {
            code: id(code, main_rows > 0, "code")?,
            main_rows,
            main_deg,
            mask_rows,
            mask_code: id(mask_code, mask_rows > 0, "mask code")?,
            answers,
        };
        s.fault().map_or(Ok(s), |f| Err(ParseError::Fault(f)))
    }
    fn write(&self, out: &mut Vec<u8>) {
        for x in [
            self.code.map_or(NONE_ID, u64::from),
            self.mask_code.map_or(NONE_ID, u64::from),
            self.main_rows,
            if self.main_rows > 0 { self.main_deg } else { 1 },
            self.mask_rows,
            u64::from(self.answers),
        ] {
            put(out, x);
        }
    }
    /// `public_fault(OracleShape)`.
    pub fn fault(&self) -> Option<&'static str> {
        if self.main_rows == 0 && self.mask_rows == 0 {
            return Some("an oracle message without rows");
        }
        if self.main_rows > 0 && self.main_deg != 1 && self.main_deg != E_DEGREE {
            return Some("an oracle message's main rows are over F or over E");
        }
        None
    }
}

/// `IndexShape` (the committed table): its code, 2^v rows, answers of the record, salt.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IndexShape {
    pub code: Code,
    pub v: u32,
    pub answers: u32,
    pub salt_bytes: u64,
}
impl IndexShape {
    pub fn rows(&self) -> u64 {
        1 << self.v
    }
    pub fn pads(&self) -> u64 {
        E_DEGREE * u64::from(self.answers)
    }
    pub fn plain(&self) -> u64 {
        self.code.ell - self.pads()
    }
    /// `index_fault`.
    pub fn fault(&self) -> Option<&'static str> {
        if !self.code.ok() {
            return Some("the table's numbers are not a code");
        }
        if self.v > 40 {
            return Some("the table has too many rows");
        }
        if self.pads() >= self.code.ell {
            return Some("a row has no room beside its pads");
        }
        if !(SALT_FLOOR_BYTES..=SALT_MOST_BYTES).contains(&self.salt_bytes)
            || self.salt_bytes % 8 != 0
        {
            return Some("the leaves of the table's tree have no admitted salt");
        }
        if self.answers < 1 {
            return Some("the table's number of answers is below 1");
        }
        None
    }
}

/// `FoldeqShape`: the table and the folded row G_u.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FoldeqShape {
    pub index: IndexShape,
    pub u: OracleShape,
    pub rows_high: bool,
    pub leaf_class: u32,
    pub columns: u64,
}
impl FoldeqShape {
    pub fn tail_first(&self) -> u64 {
        let step = 1_u64 << self.index.code.log_r();
        self.index.code.ell.div_ceil(step) * step
    }
    pub fn entries(&self) -> u64 {
        self.tail_first() + self.index.code.r
    }
    /// `public_fault(FoldeqShape)`.
    pub fn fault(&self) -> Option<&'static str> {
        if let Some(f) = self.index.fault().or(self.u.fault()) {
            return Some(f);
        }
        if self.u.main_rows == 0 || self.u.main_deg != E_DEGREE {
            return Some("the folded row's oracle message has no main rows over E");
        }
        if self.u.answers < 1 {
            return Some("the folded row's oracle message has no sample (answers = 0)");
        }
        if self.columns < 1 {
            return Some("no column is drawn");
        }
        None
    }
}

/// `IoppStage`: one stage of a proximity test.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IoppStage {
    pub code: u32,
    pub mask_code: u32,
    pub k: u32,
    pub h: u32,
}

/// `LinShape` (bound as `the test on the table`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinShape {
    pub fold: FoldeqShape,
    pub k_lo: u32,
    pub matrix_rows: u64,
    pub omega: OracleShape,
    pub w: OracleShape,
    pub omega_rows_high: bool,
    pub w_rows_high: bool,
    pub shared_split: OracleShape,
    pub own_split: OracleShape,
    pub omega_leaf_class: u32,
    pub shared_split_leaf_class: u32,
    pub w_leaf_class: u32,
    pub own_split_leaf_class: u32,
    pub shared_mask_code: u32,
    pub own_mask_code: u32,
    pub masks_ahead: bool,
    pub test_u: Vec<IoppStage>,
    pub test_omega: Vec<IoppStage>,
    pub test_own: Vec<IoppStage>,
    pub test_own_omega: Vec<IoppStage>,
    /// `IoppChoice::masks_ride`.
    pub masks_ride: bool,
}

/// An `OracleShape` field that a split leaves unused is still written: the
/// reference writes the default shape (no rows). That default fails
/// `public_fault(OracleShape)`, so unused split shapes are read without it.
fn read_split(w: &mut Words<'_>) -> Result<OracleShape, ParseError> {
    let (code, mask_code, main_rows, main_deg, mask_rows, answers) = (
        w.word()?,
        w.word()?,
        w.word()?,
        w.word()?,
        w.word()?,
        w.u32("answers")?,
    );
    if main_rows == 0 && mask_rows == 0 {
        if code != NONE_ID || mask_code != NONE_ID || main_deg != 1 {
            return Err(ParseError::Fault(
                "an unused split shape is written as the empty shape",
            ));
        }
        return Ok(OracleShape {
            code: None,
            main_rows: 0,
            main_deg: 1,
            mask_rows: 0,
            mask_code: None,
            answers,
        });
    }
    let mut v = Vec::new();
    for x in [
        code,
        mask_code,
        main_rows,
        main_deg,
        mask_rows,
        u64::from(answers),
    ] {
        put(&mut v, x);
    }
    OracleShape::read(&mut Words::new(&v))
}

impl LinShape {
    pub fn k_col(&self) -> u32 {
        self.k_lo + self.fold.index.v
    }
    pub fn k_row(&self) -> u32 {
        crate::code::ceil_log2(self.matrix_rows)
    }
    pub fn shared_split_needed(&self) -> bool {
        self.fold.u.code != self.omega.code
    }
    pub fn own_split_needed(&self) -> bool {
        self.w.code != self.omega.code
    }

    /// Parses the bound item `the test on the table`. Rejects trailing bytes,
    /// a non-canonical encoding, and every fault of `public_fault(LinShape)`.
    pub fn parse(bytes: &[u8]) -> Result<Self, ParseError> {
        let mut w = Words::new(bytes);
        let index = IndexShape {
            code: read_code(&mut w)?,
            v: w.u32("v")?,
            answers: w.u32("answers")?,
            salt_bytes: w.word()?,
        };
        let fold = FoldeqShape {
            index,
            u: OracleShape::read(&mut w)?,
            rows_high: w.bool("rows_high")?,
            leaf_class: w.u32("leaf class")?,
            columns: w.word()?,
        };
        let k_lo = w.u32("k_lo")?;
        let matrix_rows = w.word()?;
        let omega = OracleShape::read(&mut w)?;
        let ow = OracleShape::read(&mut w)?;
        let omega_rows_high = w.bool("omega_rows_high")?;
        let w_rows_high = w.bool("w_rows_high")?;
        let shared_split = read_split(&mut w)?;
        let own_split = read_split(&mut w)?;
        let classes = [
            w.u32("leaf class")?,
            w.u32("leaf class")?,
            w.u32("leaf class")?,
            w.u32("leaf class")?,
        ];
        let shared_mask_code = w.u32("mask code")?;
        let own_mask_code = w.u32("mask code")?;
        let masks_ahead = w.bool("masks_ahead")?;
        let mut tests = Vec::with_capacity(4);
        for _ in 0..4 {
            let n = w.len(64, "stages")?;
            let mut t = Vec::with_capacity(n);
            for _ in 0..n {
                let s = IoppStage {
                    code: w.u32("code")?,
                    mask_code: w.u32("mask code")?,
                    k: w.u32("k")?,
                    h: w.u32("h")?,
                };
                if s.k > MOST_LOG_N || s.h > s.k {
                    return Err(ParseError::Fault(
                        "too many row variables, or more mask rows than main rows",
                    ));
                }
                t.push(s);
            }
            tests.push(t);
        }
        let masks_ride = w.bool("masks_ride")?;
        w.end()?;
        let mut tests = tests.into_iter();
        let s = Self {
            fold,
            k_lo,
            matrix_rows,
            omega,
            w: ow,
            omega_rows_high,
            w_rows_high,
            shared_split,
            own_split,
            omega_leaf_class: classes[0],
            shared_split_leaf_class: classes[1],
            w_leaf_class: classes[2],
            own_split_leaf_class: classes[3],
            shared_mask_code,
            own_mask_code,
            masks_ahead,
            test_u: tests.next().expect("4"),
            test_omega: tests.next().expect("4"),
            test_own: tests.next().expect("4"),
            test_own_omega: tests.next().expect("4"),
            masks_ride,
        };
        s.fault().map_or(Ok(s), |f| Err(ParseError::Fault(f)))
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        let f = &self.fold;
        write_code(&f.index.code, &mut out);
        for x in [
            u64::from(f.index.v),
            u64::from(f.index.answers),
            f.index.salt_bytes,
        ] {
            put(&mut out, x);
        }
        f.u.write(&mut out);
        for x in [
            u64::from(f.rows_high),
            u64::from(f.leaf_class),
            f.columns,
            u64::from(self.k_lo),
            self.matrix_rows,
        ] {
            put(&mut out, x);
        }
        self.omega.write(&mut out);
        self.w.write(&mut out);
        put(&mut out, u64::from(self.omega_rows_high));
        put(&mut out, u64::from(self.w_rows_high));
        self.shared_split.write(&mut out);
        self.own_split.write(&mut out);
        for x in [
            self.omega_leaf_class,
            self.shared_split_leaf_class,
            self.w_leaf_class,
            self.own_split_leaf_class,
            self.shared_mask_code,
            self.own_mask_code,
        ] {
            put(&mut out, u64::from(x));
        }
        put(&mut out, u64::from(self.masks_ahead));
        for t in [
            &self.test_u,
            &self.test_omega,
            &self.test_own,
            &self.test_own_omega,
        ] {
            put(&mut out, t.len() as u64);
            for s in t {
                for x in [s.code, s.mask_code, s.k, s.h] {
                    put(&mut out, u64::from(x));
                }
            }
        }
        put(&mut out, u64::from(self.masks_ride));
        out
    }

    /// `public_fault(LinShape)`.
    pub fn fault(&self) -> Option<&'static str> {
        if let Some(f) = self.fold.fault() {
            return Some(f);
        }
        if self.matrix_rows < 1 || self.k_lo > 30 || self.k_row() > 30 || self.k_col() > 60 {
            return Some("the matrix has no rows, or too many rows or columns");
        }
        if self
            .matrix_rows
            .checked_shl(self.k_lo)
            .is_none_or(|x| x > self.fold.index.plain())
        {
            return Some("the matrix does not fit the table's rows beside their pads");
        }
        for o in [&self.omega, &self.w] {
            if let Some(f) = o.fault() {
                return Some(f);
            }
            if o.main_rows == 0 || o.main_deg != E_DEGREE {
                return Some("an oracle message of the test has no main rows over E");
            }
            if o.answers < 1 {
                return Some("an oracle message of the test is not sampled");
            }
        }
        if self.fold.u.mask_rows > 0 && self.fold.u.mask_code != Some(self.shared_mask_code) {
            return Some("the folded row's mask rows have another code than its group");
        }
        if self.w.mask_rows > 0 && self.w.mask_code != Some(self.own_mask_code) {
            return Some("W's mask rows have another code than its group");
        }
        if self.omega.mask_rows > 0 {
            return Some("Omega has mask rows; it is a member of groups with different mask codes and may have main rows only");
        }
        if self.shared_split_needed() && self.omega_leaf_class == self.shared_split_leaf_class {
            return Some("Omega and the shared split's mask message have one leaf class; they are read at different lists");
        }
        if self.own_split_needed() && self.w_leaf_class == self.own_split_leaf_class {
            return Some("W and a request's split's mask message have one leaf class; they are read at different lists");
        }
        for (needed, o, code) in [
            (
                self.shared_split_needed(),
                &self.shared_split,
                self.shared_mask_code,
            ),
            (self.own_split_needed(), &self.own_split, self.own_mask_code),
        ] {
            if needed
                && (o.main_rows != 0
                    || o.mask_rows == 0
                    || o.answers < 1
                    || o.mask_code != Some(code))
            {
                return Some("a split needs a sampled message of mask rows alone, under its groups' mask code");
            }
        }
        None
    }

    /// The faults of `lin_fault` / `foldeq_fault` / `iopp_fault` that need only
    /// the codes. See the module comment for those not yet ported.
    pub fn fault_with(&self, codes: &Codes) -> Option<&'static str> {
        if let Some(f) = self.fault() {
            return Some(f);
        }
        let base = |c: Option<u32>| c.is_some_and(|c| (c as usize) < codes.base.len());
        if !base(self.fold.u.code) {
            return Some("the folded row's oracle message names a code that is not there");
        }
        if !base(self.omega.code) || !base(self.w.code) {
            return Some("an oracle message of the test names a code that is not there");
        }
        if self.shared_mask_code as usize >= codes.mask.len()
            || self.own_mask_code as usize >= codes.mask.len()
        {
            return Some("a group of the test names a mask code that is not there");
        }
        for t in [
            &self.test_u,
            &self.test_omega,
            &self.test_own,
            &self.test_own_omega,
        ] {
            if t.is_empty() {
                continue; // a test that runs only where a split is needed
            }
            if t.len() < 2 {
                return Some("a proximity test has fewer than two stages");
            }
            for (i, s) in t.iter().enumerate() {
                let (Some(c), Some(zk)) = (
                    codes.base.get(s.code as usize),
                    codes.mask.get(s.mask_code as usize),
                ) else {
                    return Some("the stage names a code that is not there");
                };
                if !c.ell.is_power_of_two() || !zk.ell.is_power_of_two() {
                    return Some("a message length is no power of two");
                }
                if zk.log_n > c.log_n {
                    return Some("the mask code is longer than the main code");
                }
                if i + 1 < t.len() && s.k < 1 {
                    return Some("a stage but the last has no row variable");
                }
                if i + 1 == t.len() && s.k != 0 {
                    return Some("the last stage has more than one main row");
                }
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hex(s: &str) -> Vec<u8> {
        let s = s.trim();
        (0..s.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
            .collect()
    }
    fn vectors() -> (Vec<u8>, Vec<u8>) {
        (
            hex(include_str!(
                "../../../tests/vectors/shared-chain.codes.hex"
            )),
            hex(include_str!(
                "../../../tests/vectors/shared-chain.lin-shape.hex"
            )),
        )
    }

    #[test]
    fn accepted_proof_codes_round_trip() {
        let (c, _) = vectors();
        let codes = Codes::parse(&c).unwrap();
        assert_eq!(codes.to_bytes(), c);
        assert_eq!((codes.base.len(), codes.mask.len()), (12, 12));
        // Trailing byte, short input, a code that is no code: all rejected.
        assert!(Codes::parse(&[&c[..], &[0]].concat()).is_err());
        assert!(Codes::parse(&c[..c.len() - 8]).is_err());
        let mut bad = c.clone();
        bad[8..16].copy_from_slice(&0_u64.to_le_bytes()); // first base code: log_n = 0
        assert!(Codes::parse(&bad).is_err());
    }

    #[test]
    fn accepted_proof_lin_shape_round_trip() {
        let (c, l) = vectors();
        let codes = Codes::parse(&c).unwrap();
        let s = LinShape::parse(&l).unwrap();
        assert_eq!(
            s.to_bytes(),
            l,
            "canonical: re-serializing gives the bound bytes"
        );
        assert_eq!(s.fault_with(&codes), None);
        // The stored table of the accepted proof: a = 23 (8 Mi positions), 2^8 rows, salt 40.
        assert_eq!(
            (
                s.fold.index.code.log_n,
                s.fold.index.v,
                s.fold.index.salt_bytes
            ),
            (23, 8, 40)
        );
        assert!(s.test_u.len() >= 2);
        // Every single-word change either fails to parse or changes the value (no two encodings).
        for i in (0..l.len()).step_by(8) {
            let mut m = l.clone();
            m[i] ^= 1;
            if let Ok(t) = LinShape::parse(&m) {
                assert_ne!(t, s, "word {} decodes to the same shape", i / 8);
                assert_eq!(t.to_bytes(), m);
            }
        }
        assert!(LinShape::parse(&[&l[..], &[0; 8]].concat()).is_err());
    }
}
