//! Protocol blocks of the H821 verifier, ported from the pinned upstream.
//!
//! This crate grows block by block (stage D7+D9: each block's shapes and
//! checks together). Present:
//!
//! * [`code`]: Reed-Solomon codes over Goldilocks, their evaluation points
//!   and factors (`blocks/code/code.h`, `blocks/code/cosets.h`).
//! * [`shapes`]: the bound public shapes of LIN, FOLDEQ and IOPP as they
//!   stand in a chain's first query (`public_bytes` in `blocks/iop/lin.h`,
//!   `foldeq.h`, `iopp.h`, `context.h`, `code.h`), parsed canonically and
//!   checked for the faults the reference checks before running.
//! * [`tensor`]: structured coefficient vectors, `Tensor` and `Form`
//!   (`blocks/iop/tensor.h`).
//! * [`relation`]: linear claims (`Row`), group layouts, the verifier's
//!   `Statement`, `add_to_group_row` and `VectorLay` (`blocks/iop/relation.h`,
//!   `foldeq.h`).
//!
//! Every parser here rejects trailing bytes and any non-canonical encoding:
//! re-serializing a parsed value gives back exactly the input bytes.

pub mod claims;
pub mod code;
pub mod ext;
pub mod foldeq;
pub mod lin;
pub mod relation;
pub mod shapes;
pub mod tensor;

/// A cursor over canonical bound bytes: little-endian 64-bit words.
pub(crate) struct Words<'a> {
    b: &'a [u8],
    at: usize,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParseError {
    Short { at: usize },
    Trailing { at: usize, len: usize },
    TooLong(&'static str),
    NotBool(&'static str),
    Overflow(&'static str),
    Fault(&'static str),
}
impl core::fmt::Display for ParseError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for ParseError {}

impl<'a> Words<'a> {
    pub(crate) fn new(b: &'a [u8]) -> Self {
        Self { b, at: 0 }
    }
    pub(crate) fn word(&mut self) -> Result<u64, ParseError> {
        let s = self
            .b
            .get(self.at..self.at + 8)
            .ok_or(ParseError::Short { at: self.at })?;
        self.at += 8;
        Ok(u64::from_le_bytes(s.try_into().expect("8 bytes")))
    }
    pub(crate) fn u32(&mut self, what: &'static str) -> Result<u32, ParseError> {
        u32::try_from(self.word()?).map_err(|_| ParseError::Overflow(what))
    }
    pub(crate) fn usize(&mut self, what: &'static str) -> Result<usize, ParseError> {
        usize::try_from(self.word()?).map_err(|_| ParseError::Overflow(what))
    }
    pub(crate) fn bool(&mut self, what: &'static str) -> Result<bool, ParseError> {
        match self.word()? {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(ParseError::NotBool(what)),
        }
    }
    pub(crate) fn len(&mut self, most: usize, what: &'static str) -> Result<usize, ParseError> {
        let n = self.usize(what)?;
        if n > most {
            return Err(ParseError::TooLong(what));
        }
        Ok(n)
    }
    pub(crate) fn end(&self) -> Result<(), ParseError> {
        if self.at != self.b.len() {
            return Err(ParseError::Trailing {
                at: self.at,
                len: self.b.len(),
            });
        }
        Ok(())
    }
}
pub(crate) fn put(out: &mut Vec<u8>, x: u64) {
    out.extend_from_slice(&x.to_le_bytes());
}
