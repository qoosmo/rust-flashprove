//! Reference arithmetic for FlashProve field 2 (Goldilocks).
//! No SIMD or Montgomery representation. No cryptographic constant-time claim.
//! Upstream: FORMAT.md R1.2–R1.4, p=2^64-2^32+1, E=F[X]/(X^3-2).

use core::fmt;

/// Prime modulus of field 2.
pub const MODULUS: u64 = 0xffff_ffff_0000_0001;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FieldError {
    WrongLength { expected: usize, actual: usize },
    NonCanonical { value: u64 },
}

impl fmt::Display for FieldError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::WrongLength { expected, actual } => {
                write!(f, "field encoding requires {expected} bytes; got {actual}")
            }
            Self::NonCanonical { value } => write!(f, "field value {value} is not canonical"),
        }
    }
}
impl std::error::Error for FieldError {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Fp(u64);

impl Fp {
    pub const ZERO: Self = Self(0);
    pub const ONE: Self = Self(1);
    pub const TWO: Self = Self(2);

    pub fn from_canonical(value: u64) -> Result<Self, FieldError> {
        if value >= MODULUS {
            Err(FieldError::NonCanonical { value })
        } else {
            Ok(Self(value))
        }
    }

    pub const fn value(self) -> u64 {
        self.0
    }

    pub fn from_le_bytes(bytes: &[u8]) -> Result<Self, FieldError> {
        let word: [u8; 8] = bytes.try_into().map_err(|_| FieldError::WrongLength {
            expected: 8,
            actual: bytes.len(),
        })?;
        Self::from_canonical(u64::from_le_bytes(word))
    }

    pub const fn to_le_bytes(self) -> [u8; 8] {
        self.0.to_le_bytes()
    }

    pub fn pow(self, mut exponent: u64) -> Self {
        let mut acc = Self::ONE;
        let mut base = self;
        while exponent != 0 {
            if exponent & 1 == 1 {
                acc *= base;
            }
            base *= base;
            exponent >>= 1;
        }
        acc
    }

    /// Multiplicative inverse; zero has no inverse.
    pub fn inverse(self) -> Option<Self> {
        if self == Self::ZERO {
            None
        } else {
            Some(self.pow(MODULUS - 2))
        }
    }
}

impl core::ops::Add for Fp {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        Self(((self.0 as u128 + rhs.0 as u128) % MODULUS as u128) as u64)
    }
}
impl core::ops::Sub for Fp {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        Self(((self.0 as u128 + MODULUS as u128 - rhs.0 as u128) % MODULUS as u128) as u64)
    }
}
impl core::ops::Mul for Fp {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        Self(((self.0 as u128 * rhs.0 as u128) % MODULUS as u128) as u64)
    }
}
impl core::ops::AddAssign for Fp {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}
impl core::ops::SubAssign for Fp {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}
impl core::ops::MulAssign for Fp {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

/// Cubic extension F[X]/(X^3-2), encoded as three little-endian field words.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Ext3(pub [Fp; 3]);

impl Ext3 {
    pub const ZERO: Self = Self([Fp::ZERO; 3]);
    pub const ONE: Self = Self([Fp::ONE, Fp::ZERO, Fp::ZERO]);

    pub fn from_le_bytes(bytes: &[u8]) -> Result<Self, FieldError> {
        if bytes.len() != 24 {
            return Err(FieldError::WrongLength {
                expected: 24,
                actual: bytes.len(),
            });
        }
        Ok(Self([
            Fp::from_le_bytes(&bytes[0..8])?,
            Fp::from_le_bytes(&bytes[8..16])?,
            Fp::from_le_bytes(&bytes[16..24])?,
        ]))
    }

    pub fn to_le_bytes(self) -> [u8; 24] {
        let mut out = [0; 24];
        for (i, coeff) in self.0.iter().enumerate() {
            out[i * 8..i * 8 + 8].copy_from_slice(&coeff.to_le_bytes());
        }
        out
    }
}
impl core::ops::Add for Ext3 {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        Self([
            self.0[0] + rhs.0[0],
            self.0[1] + rhs.0[1],
            self.0[2] + rhs.0[2],
        ])
    }
}
impl core::ops::Mul for Ext3 {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        let [a, b, c] = self.0;
        let [d, e, f] = rhs.0;
        Self([
            a * d + Fp::TWO * (b * f + c * e),
            a * e + b * d + Fp::TWO * c * f,
            a * f + b * e + c * d,
        ])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonical_boundaries() {
        assert_eq!(
            Fp::from_canonical(MODULUS - 1).unwrap().value(),
            MODULUS - 1
        );
        assert_eq!(
            Fp::from_canonical(MODULUS),
            Err(FieldError::NonCanonical { value: MODULUS })
        );
        assert!(Fp::from_le_bytes(&[0; 7]).is_err());
    }

    #[test]
    fn arithmetic_modulus() {
        let minus_one = Fp::from_canonical(MODULUS - 1).unwrap();
        assert_eq!(minus_one + Fp::ONE, Fp::ZERO);
        assert_eq!(Fp::ZERO - Fp::ONE, minus_one);
        assert_eq!(minus_one * minus_one, Fp::ONE);
        assert_eq!(Fp::TWO.inverse().unwrap() * Fp::TWO, Fp::ONE);
        assert_eq!(Fp::ZERO.inverse(), None);
    }

    #[test]
    fn extension_relation() {
        let x = Ext3([Fp::ZERO, Fp::ONE, Fp::ZERO]);
        let x2 = x * x;
        assert_eq!(x2, Ext3([Fp::ZERO, Fp::ZERO, Fp::ONE]));
        assert_eq!(x2 * x, Ext3([Fp::TWO, Fp::ZERO, Fp::ZERO]));
        assert_eq!(Ext3::from_le_bytes(&x.to_le_bytes()), Ok(x));
    }

    #[test]
    fn randomish_ring_properties() {
        for i in 0_u64..1024 {
            let a = Fp::from_canonical(i * 1_000_003).unwrap();
            let b = Fp::from_canonical(i * 2_000_003).unwrap();
            let c = Fp::from_canonical(i * 3_000_017).unwrap();
            assert_eq!((a + b) + c, a + (b + c));
            assert_eq!(a * (b + c), a * b + a * c);
        }
    }
}
