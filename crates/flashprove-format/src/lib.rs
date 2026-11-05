//! Byte-oriented *pre-verification* parsing for FlashProve H821.
//!
//! This crate does not determine validity of a FlashProve proof. Proof files
//! have no length field; their remaining bytes are interpreted according to
//! a statement-dependent, round-by-round verification plan (FORMAT.md R14.x).

use flashprove_field::{Ext3, FieldError, Fp};
use std::fmt;

pub const VERSION: [u8; 4] = *b"H821";
pub const PROOF_TAG: [u8; 4] = *b"CPPF";
pub const KEY_TAG: [u8; 4] = *b"CPIK";
pub const LEAF_TAG: [u8; 4] = *b"CPEN";

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FormatError {
    UnexpectedEof {
        offset: usize,
        needed: usize,
        remaining: usize,
    },
    WrongTag {
        expected: [u8; 4],
        got: [u8; 4],
    },
    WrongVersion {
        got: [u8; 4],
    },
    NotWordAligned {
        byte_len: usize,
        word_size: usize,
    },
    TooManyWords {
        words: usize,
        limit: usize,
    },
    MissingTokens,
    InvalidWindow {
        start: u32,
        end: u32,
        tokens: usize,
    },
    UnexpectedToken {
        token: u32,
        end: u32,
        tokens: usize,
    },
    NonCanonicalField(FieldError),
    WrongPolicyVersion,
    InvalidUtf8,
    TrailingBytes {
        count: usize,
    },
}
impl fmt::Display for FormatError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnexpectedEof {
                offset,
                needed,
                remaining,
            } => write!(f, "offset {offset}: need {needed} bytes; have {remaining}"),
            Self::WrongTag { expected, got } => {
                write!(f, "wrong file tag: expected {expected:?}, got {got:?}")
            }
            Self::WrongVersion { got } => write!(f, "unsupported version {got:?}; only H821"),
            Self::NotWordAligned {
                byte_len,
                word_size,
            } => write!(f, "{byte_len} bytes not aligned to {word_size}-byte words"),
            Self::TooManyWords { words, limit } => {
                write!(f, "{words} words exceed configured limit {limit}")
            }
            Self::MissingTokens => {
                write!(f, "request must contain at least one token plus r and e")
            }
            Self::InvalidWindow { start, end, tokens } => write!(
                f,
                "request window r={start}, e={end} out of range for T={tokens}"
            ),
            Self::UnexpectedToken { token, end, tokens } => write!(
                f,
                "next-token file is {token}, but e={end} < T={tokens}, so it must be zero"
            ),
            Self::NonCanonicalField(e) => write!(f, "{e}"),
            Self::WrongPolicyVersion => write!(f, "policy first line must be 'version H821'"),
            Self::InvalidUtf8 => write!(f, "configuration text is not UTF-8"),
            Self::TrailingBytes { count } => write!(f, "{count} unexpected trailing bytes"),
        }
    }
}
impl std::error::Error for FormatError {}
impl From<FieldError> for FormatError {
    fn from(error: FieldError) -> Self {
        Self::NonCanonicalField(error)
    }
}

/// Checked, non-allocating cursor for big buffers.
#[derive(Debug, Clone)]
pub struct Cursor<'a> {
    bytes: &'a [u8],
    position: usize,
}
impl<'a> Cursor<'a> {
    pub fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, position: 0 }
    }
    pub fn position(&self) -> usize {
        self.position
    }
    pub fn remaining(&self) -> usize {
        self.bytes.len() - self.position
    }
    pub fn read(&mut self, count: usize) -> Result<&'a [u8], FormatError> {
        let start = self.position;
        let end = start.checked_add(count).ok_or(FormatError::UnexpectedEof {
            offset: start,
            needed: count,
            remaining: self.remaining(),
        })?;
        let part = self
            .bytes
            .get(start..end)
            .ok_or(FormatError::UnexpectedEof {
                offset: start,
                needed: count,
                remaining: self.remaining(),
            })?;
        self.position = end;
        Ok(part)
    }
    pub fn read_u32(&mut self) -> Result<u32, FormatError> {
        let x: [u8; 4] = self.read(4)?.try_into().expect("read exactly 4");
        Ok(u32::from_le_bytes(x))
    }
    pub fn read_u64(&mut self) -> Result<u64, FormatError> {
        let x: [u8; 8] = self.read(8)?.try_into().expect("read exactly 8");
        Ok(u64::from_le_bytes(x))
    }
    pub fn read_field(&mut self) -> Result<Fp, FormatError> {
        Ok(Fp::from_le_bytes(self.read(8)?)?)
    }
    pub fn read_extension(&mut self) -> Result<Ext3, FormatError> {
        Ok(Ext3::from_le_bytes(self.read(24)?)?)
    }
    pub fn finish(self) -> Result<(), FormatError> {
        if self.remaining() != 0 {
            Err(FormatError::TrailingBytes {
                count: self.remaining(),
            })
        } else {
            Ok(())
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProofHeader {
    pub leaf_index: u32,
}
impl ProofHeader {
    /// Serializes exactly the 12-byte protocol header, not any proof body.
    pub fn to_bytes(self) -> [u8; 12] {
        let mut bytes = [0_u8; 12];
        bytes[0..4].copy_from_slice(&PROOF_TAG);
        bytes[4..8].copy_from_slice(&VERSION);
        bytes[8..12].copy_from_slice(&self.leaf_index.to_le_bytes());
        bytes
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProofEnvelope<'a> {
    pub header: ProofHeader,
    pub unverified_body: &'a [u8],
}

/// Parses *only* the header and exposes the remainder as unverified opaque bytes.
/// Header = 4 ASCII bytes CPPF | 4 ASCII bytes H821 | LE u32 leaf index.
pub fn parse_proof(bytes: &[u8]) -> Result<ProofEnvelope<'_>, FormatError> {
    let mut cur = Cursor::new(bytes);
    check_header(&mut cur, PROOF_TAG)?;
    let leaf_index = cur.read_u32()?;
    Ok(ProofEnvelope {
        header: ProofHeader { leaf_index },
        unverified_body: &bytes[cur.position()..],
    })
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct KeyEnvelope<'a> {
    pub unverified_body: &'a [u8],
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LeafEnvelope<'a> {
    pub unverified_body: &'a [u8],
}

pub fn parse_key(bytes: &[u8]) -> Result<KeyEnvelope<'_>, FormatError> {
    let mut cur = Cursor::new(bytes);
    check_header(&mut cur, KEY_TAG)?;
    Ok(KeyEnvelope {
        unverified_body: &bytes[cur.position()..],
    })
}
pub fn parse_leaf(bytes: &[u8]) -> Result<LeafEnvelope<'_>, FormatError> {
    let mut cur = Cursor::new(bytes);
    check_header(&mut cur, LEAF_TAG)?;
    Ok(LeafEnvelope {
        unverified_body: &bytes[cur.position()..],
    })
}
fn check_header(cur: &mut Cursor<'_>, expected: [u8; 4]) -> Result<(), FormatError> {
    let tag: [u8; 4] = cur.read(4)?.try_into().expect("read exactly 4");
    if tag != expected {
        return Err(FormatError::WrongTag { expected, got: tag });
    }
    let version: [u8; 4] = cur.read(4)?.try_into().expect("read exactly 4");
    if version != VERSION {
        return Err(FormatError::WrongVersion { got: version });
    }
    Ok(())
}

/// Request = T token IDs, followed by r and e; every word is LE u32.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Request {
    pub tokens: Vec<u32>,
    pub r: u32,
    pub e: u32,
}
impl Request {
    /// Lossless serialization of the request's T+2 little-endian u32 words.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity((self.tokens.len() + 2) * 4);
        for token in &self.tokens {
            bytes.extend_from_slice(&token.to_le_bytes());
        }
        bytes.extend_from_slice(&self.r.to_le_bytes());
        bytes.extend_from_slice(&self.e.to_le_bytes());
        bytes
    }

    /// `limit` caps T to avoid unbounded allocations on hostile inputs.
    pub fn parse(bytes: &[u8], limit: usize) -> Result<Self, FormatError> {
        let words = parse_u32_words(bytes, limit.saturating_add(2))?;
        if words.len() < 3 {
            return Err(FormatError::MissingTokens);
        }
        let n = words.len();
        Ok(Self {
            tokens: words[..n - 2].to_vec(),
            r: words[n - 2],
            e: words[n - 1],
        })
    }
    /// Optional semantic check for a nonempty checked interval, separate from parsing.
    pub fn validate_window(&self) -> Result<(), FormatError> {
        let t = self.tokens.len();
        if self.r as usize >= t || self.e as usize > t || self.r >= self.e {
            return Err(FormatError::InvalidWindow {
                start: self.r,
                end: self.e,
                tokens: t,
            });
        }
        Ok(())
    }
    pub fn validate_next_token(&self, next: u32) -> Result<(), FormatError> {
        if (self.e as usize) < self.tokens.len() && next != 0 {
            return Err(FormatError::UnexpectedToken {
                token: next,
                end: self.e,
                tokens: self.tokens.len(),
            });
        }
        Ok(())
    }
}

pub fn parse_u32_words(bytes: &[u8], limit: usize) -> Result<Vec<u32>, FormatError> {
    if bytes.len() % 4 != 0 {
        return Err(FormatError::NotWordAligned {
            byte_len: bytes.len(),
            word_size: 4,
        });
    }
    let words = bytes.len() / 4;
    if words > limit {
        return Err(FormatError::TooManyWords { words, limit });
    }
    Ok(bytes
        .chunks_exact(4)
        .map(|c| u32::from_le_bytes(c.try_into().expect("4-byte chunk")))
        .collect())
}

pub fn parse_next_token(bytes: &[u8]) -> Result<u32, FormatError> {
    let mut cur = Cursor::new(bytes);
    let next = cur.read_u32()?;
    cur.finish()?;
    Ok(next)
}

/// Checks only the first policy line. Full parameter-policy validation is future work.
pub fn check_policy_version(bytes: &[u8]) -> Result<(), FormatError> {
    let raw = std::str::from_utf8(bytes).map_err(|_| FormatError::InvalidUtf8)?;
    if raw.lines().next() == Some("version H821") {
        Ok(())
    } else {
        Err(FormatError::WrongPolicyVersion)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn proof_header_exact_and_leaf_index() {
        let p = b"CPPFH821\x05\x00\x00\x00opaque";
        let got = parse_proof(p).unwrap();
        assert_eq!(got.header.leaf_index, 5);
        assert_eq!(&got.header.to_bytes()[..], &p[..12]);
        assert_eq!(got.unverified_body, b"opaque");
        assert_eq!(
            parse_proof(&p[..11]),
            Err(FormatError::UnexpectedEof {
                offset: 8,
                needed: 4,
                remaining: 3
            })
        );
    }

    #[test]
    fn proof_bad_tag_and_version_fail() {
        let mut p = *b"CPPFH821\x00\x00\x00\x00";
        p[0] = b'X';
        assert!(matches!(parse_proof(&p), Err(FormatError::WrongTag { .. })));
        p[0] = b'C';
        p[4] = b'X';
        assert!(matches!(
            parse_proof(&p),
            Err(FormatError::WrongVersion { .. })
        ));
    }

    #[test]
    fn root_headers() {
        assert!(parse_key(b"CPIKH821").is_ok());
        assert!(parse_leaf(b"CPENH821").is_ok());
        assert!(parse_leaf(b"CPIKH821").is_err());
    }

    #[test]
    fn request_boundary_checks() {
        let mut v = Vec::new();
        for x in [2_u32, 4, 6, 1, 3] {
            v.extend_from_slice(&x.to_le_bytes());
        }
        let req = Request::parse(&v, 3).unwrap();
        assert_eq!(req.tokens, vec![2, 4, 6]);
        assert!(req.validate_window().is_ok());
        assert!(Request::parse(&v, 2).is_err());
        assert!(Request::parse(&v[..v.len() - 1], 3).is_err());
        assert!(req.validate_next_token(0).is_ok());
        assert!(req.validate_next_token(10).is_ok());
        let mut partial = req.clone();
        partial.e = 2;
        assert!(partial.validate_window().is_ok());
        assert!(partial.validate_next_token(0).is_ok());
        assert!(matches!(
            partial.validate_next_token(10),
            Err(FormatError::UnexpectedToken { .. })
        ));
    }

    #[test]
    fn exact_y_and_strict_cursor() {
        assert_eq!(parse_next_token(&199_u32.to_le_bytes()), Ok(199));
        assert!(matches!(
            parse_next_token(&[0; 8]),
            Err(FormatError::TrailingBytes { count: 4 })
        ));
        let mut cur = Cursor::new(&[0; 16]);
        assert!(cur.read(usize::MAX).is_err());
        assert_eq!(cur.position(), 0);
        assert!(cur.read(17).is_err());
        assert_eq!(cur.position(), 0);
    }

    #[test]
    fn field_reads_canonical_only() {
        let bytes = flashprove_field::MODULUS.to_le_bytes();
        let mut cur = Cursor::new(&bytes);
        assert!(matches!(
            cur.read_field(),
            Err(FormatError::NonCanonicalField(_))
        ));
    }

    #[test]
    fn truncated_proof_header_never_panics() {
        let good = b"CPPFH821\0\0\0\0";
        for end in 0..good.len() {
            assert!(parse_proof(&good[..end]).is_err());
        }
        assert!(parse_proof(good).is_ok()); // header-only is NOT a valid proof
    }

    #[test]
    fn actual_upstream_request_vector() {
        // From upstream examples/accepted-proof/example.req and example.y at the pinned commit.
        let request = include_bytes!("../../../tests/vectors/upstream-example.req");
        let reply = include_bytes!("../../../tests/vectors/upstream-example.y");
        let r = Request::parse(request, 1_000).unwrap();
        assert_eq!((r.tokens.len(), r.r, r.e), (64, 60, 64));
        assert_eq!(r.to_bytes().as_slice(), &request[..]);
        r.validate_window().unwrap();
        let next = parse_next_token(reply).unwrap();
        assert_eq!(next, 199);
        r.validate_next_token(next).unwrap();
    }
}
