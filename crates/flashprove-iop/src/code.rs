//! Reed-Solomon codes over Goldilocks (`blocks/code/code.h`, `blocks/code/cosets.h`).
//!
//! A code of length $2^{a}$ uses $2^{a-s}$ cosets of the subgroup $H$ of order
//! $2^s$, $s = \min(a, 32)$. With $g = 7$ (a generator of $\mathbb F_p^\times$)
//! and $w$ = [`ROOT_32`] of order $2^{32}$, position $I$ has the point
//! $$z_I = g^{1+c}\prod_{i<s,\ \text{bit } i \text{ of } I = 1} w^{2^{31-i}},\qquad c = I \gg s.$$
//! Positions $2m$ and $2m+1$ have the points $z$ and $-z$; no point is $0$.
//! The factors at $z$ are $f_i = z^{2^i}$.

use crate::{put, ParseError, Words};
use flashprove_field::Fp;

pub const GENERATOR: u64 = 7;
/// $7^{5(2^{32}-1)}$, of order $2^{32}$.
pub const ROOT_32: u64 = 0xE2AF_7063_5744_FD26;
pub const SUBGROUP_LOG: u32 = 32;
pub const MOST_LOG_N: u32 = 60;
/// `NONE_ID` of `blocks/iop/relation.h`.
pub const NONE_ID: u64 = u32::MAX as u64;

/// The least $a$ with $2^a \ge v$ (`ceil_log2`, blocks/base.h; 0 for v <= 1).
pub fn ceil_log2(v: u64) -> u32 {
    let mut a = 0;
    while a < 64 && (1_u64 << a) < v {
        a += 1;
    }
    a
}
pub fn subgroup_log(log_n: u32) -> u32 {
    log_n.min(SUBGROUP_LOG)
}

/// `Code`: length $2^{\text{log\_n}}$, `ell` message entries, `r` random (tail) entries.
/// Tail coefficients are $0..r-1$, message entry $j$ is coefficient $r+j$.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Code {
    pub log_n: u32,
    pub ell: u64,
    pub r: u64,
}
impl Code {
    pub fn n(&self) -> u64 {
        1 << self.log_n
    }
    pub fn dim(&self) -> u64 {
        self.ell + self.r
    }
    pub fn log_dim(&self) -> u32 {
        ceil_log2(self.dim())
    }
    pub fn log_ell(&self) -> u32 {
        ceil_log2(self.ell)
    }
    pub fn log_r(&self) -> u32 {
        ceil_log2(self.r)
    }
    pub fn message_at(&self) -> u64 {
        self.r
    }
    /// `code_ok`: the three numbers describe a code whose dimension fits one coset.
    pub fn ok(&self) -> bool {
        if self.log_n < 1 || self.log_n > MOST_LOG_N || self.ell < 1 {
            return false;
        }
        let n = self.n();
        let Some(dim) = self.ell.checked_add(self.r) else {
            return false;
        };
        if self.ell > n || self.r > n || dim > n {
            return false;
        }
        dim <= 1_u64 << subgroup_log(self.log_n)
    }
    /// Two different codewords differ in at least this many positions.
    pub fn min_distance(&self) -> u64 {
        self.n() - self.dim() + 1
    }
    /// With a uniform tail, the symbols at this many distinct positions hide the message.
    pub fn hiding_positions(&self) -> u64 {
        self.r
    }
    fn read(w: &mut Words<'_>) -> Result<Self, ParseError> {
        Ok(Self {
            log_n: w.u32("log_n")?,
            ell: w.word()?,
            r: w.word()?,
        })
    }
    fn write(&self, out: &mut Vec<u8>) {
        put(out, u64::from(self.log_n));
        put(out, self.ell);
        put(out, self.r);
    }
}

/// $z_I$ for a code of length $2^{\text{log\_n}}$ (`gl64_point`).
pub fn point(log_n: u32, i: u64) -> Fp {
    let s = subgroup_log(log_n);
    let mut z = Fp::from_canonical(GENERATOR).expect("7").pow(1 + (i >> s));
    let mut root = Fp::from_canonical(ROOT_32).expect("canonical");
    for bit in (0..32).rev() {
        if bit < s && (i >> bit) & 1 == 1 {
            z *= root;
        }
        root *= root;
    }
    z
}
/// $f_i = z_I^{2^i}$ for $i <$ `count` (`gl64_factors`).
pub fn factors(log_n: u32, i: u64, count: u32) -> Vec<Fp> {
    let mut f = Vec::with_capacity(count as usize);
    if count > 0 {
        f.push(point(log_n, i));
    }
    for k in 1..count as usize {
        f.push(f[k - 1] * f[k - 1]);
    }
    f
}

/// `Codes`: the base (main) codes and the mask codes, by `CodeId`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Codes {
    pub base: Vec<Code>,
    pub mask: Vec<Code>,
}
impl Codes {
    /// The bound item `codes` (`public_bytes(Codes)`): two lists of (log_n, ell, r).
    /// Rejects trailing bytes and any list entry that is no code (`public_fault(Codes)`).
    pub fn parse(bytes: &[u8]) -> Result<Self, ParseError> {
        let mut w = Words::new(bytes);
        let list = |w: &mut Words<'_>| -> Result<Vec<Code>, ParseError> {
            let n = w.len(1 << 16, "codes")?;
            (0..n).map(|_| Code::read(w)).collect()
        };
        let base = list(&mut w)?;
        let mask = list(&mut w)?;
        w.end()?;
        if base.iter().chain(&mask).any(|c| !c.ok()) {
            return Err(ParseError::Fault(
                "a code's numbers are no code of this field",
            ));
        }
        Ok(Self { base, mask })
    }
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        for list in [&self.base, &self.mask] {
            put(&mut out, list.len() as u64);
            for c in list {
                c.write(&mut out);
            }
        }
        out
    }
}
pub(crate) fn read_code(w: &mut Words<'_>) -> Result<Code, ParseError> {
    Code::read(w)
}
pub(crate) fn write_code(c: &Code, out: &mut Vec<u8>) {
    c.write(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn generator_and_root() {
        let p1 = flashprove_field::MODULUS - 1; // 2^32 (2^32 - 1)
        let g = Fp::from_canonical(GENERATOR).unwrap();
        // 7 generates F_p^*: 7^((p-1)/q) != 1 for every prime q | p - 1 = 2^32 * 3 * 5 * 17 * 257 * 65537.
        for q in [2_u64, 3, 5, 17, 257, 65537] {
            assert_ne!(g.pow(p1 / q), Fp::ONE, "q = {q}");
        }
        let w = Fp::from_canonical(ROOT_32).unwrap();
        assert_eq!(w, g.pow(5 * ((1_u64 << 32) - 1)));
        assert_eq!(w.pow(1 << 32), Fp::ONE);
        assert_ne!(w.pow(1 << 31), Fp::ONE);
        // Powers of orders 64, 32, 16, 8, 4 are 2^3, 2^6, 2^12, 2^24, 2^48.
        for (k, e) in [(26, 3), (27, 6), (28, 12), (29, 24), (30, 48)] {
            assert_eq!(
                w.pow(1 << k),
                Fp::from_canonical(1 << e).unwrap(),
                "w^(2^{k})"
            );
        }
    }

    #[test]
    fn points_pair_and_cosets() {
        for log_n in [1, 5, 13, 23] {
            for m in [0_u64, 1, 7, (1 << (log_n - 1)) - 1] {
                let (z0, z1) = (point(log_n, 2 * m), point(log_n, 2 * m + 1));
                assert_eq!(z0 + z1, Fp::ZERO, "z_(2m+1) = -z_(2m)");
                assert_ne!(z0, Fp::ZERO);
            }
            // All points of a short code are distinct and their 2^log_n-th powers agree (one coset).
            if log_n <= 13 {
                let pts: Vec<Fp> = (0..1 << log_n).map(|i| point(log_n, i)).collect();
                let mut v: Vec<u64> = pts.iter().map(|z| z.value()).collect();
                v.sort_unstable();
                v.dedup();
                assert_eq!(v.len(), 1 << log_n);
                let c = pts[0].pow(1 << log_n);
                assert!(pts.iter().all(|z| z.pow(1 << log_n) == c));
            }
        }
        // Beyond 2^32 points the coset index is the high bits.
        assert_eq!(
            point(33, 1 << 32),
            Fp::from_canonical(GENERATOR).unwrap().pow(2)
        );
        let f = factors(10, 37, 5);
        for i in 1..5 {
            assert_eq!(f[i], f[i - 1] * f[i - 1]);
        }
    }

    /// Differential: upstream `gl64_point` (scripts/points_cpp_oracle.cpp) at 48 positions.
    #[test]
    fn points_equal_upstream() {
        for line in include_str!("../../../tests/vectors/gl64-points.txt").lines() {
            let v: Vec<u64> = line.split(' ').map(|x| x.parse().unwrap()).collect();
            assert_eq!(
                point(v[0] as u32, v[1]).value(),
                v[2],
                "log_n {} position {}",
                v[0],
                v[1]
            );
        }
    }

    #[test]
    fn code_ok_bounds() {
        assert!(Code {
            log_n: 4,
            ell: 8,
            r: 8
        }
        .ok());
        assert!(!Code {
            log_n: 4,
            ell: 9,
            r: 8
        }
        .ok());
        assert!(!Code {
            log_n: 0,
            ell: 1,
            r: 0
        }
        .ok());
        assert!(!Code {
            log_n: 4,
            ell: 0,
            r: 1
        }
        .ok());
        assert!(!Code {
            log_n: 61,
            ell: 1,
            r: 0
        }
        .ok());
        assert!(
            !Code {
                log_n: 40,
                ell: (1 << 32) + 1,
                r: 0
            }
            .ok(),
            "dimension beyond one coset"
        );
        assert_eq!(
            Code {
                log_n: 4,
                ell: 3,
                r: 2
            }
            .min_distance(),
            12
        );
        assert_eq!(ceil_log2(1), 0);
        assert_eq!(ceil_log2(5), 3);
        assert_eq!(ceil_log2(8), 3);
    }
}
