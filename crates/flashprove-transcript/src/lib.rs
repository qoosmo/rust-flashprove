//! Reference byte-level FlashProve H821 Fiat-Shamir transcript primitives.
//!
//! Grounded in upstream FORMAT.md R2.1-R2.3, R4.5-R4.6, R5.2-R5.5,
//! R6.1-R6.9 at the pinned upstream revision.
//!
//! Not a proof verifier: this crate does not bind a public statement, plan,
//! proof-body layout, Merkle openings, or commitment checks.

use blake2b_simd::Params;
use flashprove_field::{Ext3, Fp, MODULUS};
use std::fmt;

pub type Digest = [u8; 32];
pub const UPSTREAM_REVISION: &str = "9e2bdd8ff5bf9c62f18263d7dac189b0400b260c";

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TranscriptError {
    InvalidDomain(u16),
    InvalidHashArguments,
    InvalidLabel(u64),
    InvalidIndex(u64),
    InvalidShape,
    OversizeMessage,
    MisalignedRoundMessage,
    InvalidWork(u8),
    UnexpectedNonce,
    WorkNotSatisfied,
    RoundOverflow,
    TooManyDraws,
    InvalidPositionWidth(u8),
}
impl fmt::Display for TranscriptError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for TranscriptError {}

/// H(number, tree, index, start; bytes), with optional leaf shape
/// (symbols, salt length in 8-byte words).
/// Domain 162 returns 64 bytes; every other permitted domain returns 32.
/// When present, start supplies BLAKE2b salt and personalization, not payload.
pub fn h(
    number: u16,
    tree: u64,
    index: u64,
    start: Option<&Digest>,
    bytes: &[u8],
    leaf_shape: Option<(u32, u8)>,
) -> Result<Vec<u8>, TranscriptError> {
    let has_start = match number {
        162 | 164 | 166 | 171 | 173 | 174 | 178 => true,
        160 | 168 | 169 | 172 | 176 | 179 => false,
        _ => return Err(TranscriptError::InvalidDomain(number)),
    };
    if has_start != start.is_some() {
        return Err(TranscriptError::InvalidHashArguments);
    }
    if index >= (1_u64 << 63) {
        return Err(TranscriptError::InvalidIndex(index));
    }
    if (number == 162 && tree >= (1_u64 << 48))
        || (number == 164 && tree >= (1_u64 << 16))
        || (number != 162 && number != 164 && tree != 0)
    {
        return Err(TranscriptError::InvalidLabel(tree));
    }
    let is_leaf = matches!(number, 164 | 173 | 174);
    if is_leaf != leaf_shape.is_some() {
        return Err(TranscriptError::InvalidShape);
    }
    let (symbols, salt_words) = leaf_shape.unwrap_or((0, 0));
    if is_leaf && (symbols == 0 || symbols >= (1 << 24) || !(5..=8).contains(&salt_words)) {
        return Err(TranscriptError::InvalidShape);
    }
    if u64::try_from(bytes.len()).map_err(|_| TranscriptError::OversizeMessage)?
        > u64::from(u32::MAX) - 144
    {
        return Err(TranscriptError::OversizeMessage);
    }
    let label = u64::from(number)
        | (tree << 16)
        | (u64::from(symbols) << 32)
        | (u64::from(salt_words) << 56);
    let mut input = Vec::with_capacity(16 + bytes.len());
    input.extend_from_slice(&label.to_le_bytes());
    input.extend_from_slice(&index.to_le_bytes());
    input.extend_from_slice(bytes);
    let mut params = Params::new();
    params.hash_length(if number == 162 { 64 } else { 32 });
    if let Some(start) = start {
        params.salt(&start[..16]);
        params.personal(&start[16..]);
    }
    Ok(params.hash(&input).as_bytes().to_vec())
}
fn as_digest(bytes: Vec<u8>) -> Digest {
    bytes.try_into().expect("32-byte hash output")
}
fn push_u64(bytes: &mut Vec<u8>, x: u64) {
    bytes.extend_from_slice(&x.to_le_bytes());
}
fn valid_label(label: u64) -> Result<(), TranscriptError> {
    if label >= (1_u64 << 48) {
        Err(TranscriptError::InvalidLabel(label))
    } else {
        Ok(())
    }
}

/// H(172, 0, label, none; parameters, random bytes).
pub fn run_value(label: u64, parameters: &Digest, random_bytes: &Digest) -> Result<Digest, TranscriptError> {
    valid_label(label)?;
    let mut bytes = Vec::with_capacity(64);
    bytes.extend_from_slice(parameters);
    bytes.extend_from_slice(random_bytes);
    Ok(as_digest(h(172, 0, label, None, &bytes, None)?))
}

/// R4.6 first query with an empty record field, as used by real proofs.
pub fn first_value(label: u64, parameters: &Digest, statement: &[u8], run: Option<&Digest>) -> Result<Digest, TranscriptError> {
    valid_label(label)?;
    let mut bytes = Vec::with_capacity(statement.len().saturating_add(64));
    bytes.extend_from_slice(parameters);
    push_u64(&mut bytes, u64::try_from(statement.len()).map_err(|_| TranscriptError::OversizeMessage)?);
    bytes.extend_from_slice(statement);
    push_u64(&mut bytes, 0);
    match run {
        Some(run) => {
            push_u64(&mut bytes, 1);
            bytes.extend_from_slice(run);
        }
        None => push_u64(&mut bytes, 0),
    }
    Ok(as_digest(h(160, 0, label, None, &bytes, None)?))
}

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RoundKind {
    Algebraic = 1,
    Epsilon = 2,
    Seed = 3,
    Positions = 4,
    Bits = 5,
    Seal = 6,
    Empty = 7,
}

/// H821 round call C_i(j): 64 bytes, never silently reduced mod p.
// Preserve the eight named protocol inputs for independent byte-level audit.
#[allow(clippy::too_many_arguments)]
pub fn round_call(
    label: u64,
    round: u64,
    rho_before: &Digest,
    prover_message: &[u8],
    kind: RoundKind,
    work_bits: u8,
    nonce: u64,
    call_number: u64,
) -> Result<[u8; 64], TranscriptError> {
    valid_label(label)?;
    if round == 0 || round >= (1_u64 << 63) {
        return Err(TranscriptError::InvalidIndex(round));
    }
    if call_number >= (1_u64 << 48) {
        return Err(TranscriptError::InvalidIndex(call_number));
    }
    if prover_message.len() % 8 != 0 {
        return Err(TranscriptError::MisalignedRoundMessage);
    }
    if work_bits > 64 || (matches!(kind, RoundKind::Seal | RoundKind::Empty) && work_bits != 0) {
        return Err(TranscriptError::InvalidWork(work_bits));
    }
    if work_bits == 0 && nonce != 0 {
        return Err(TranscriptError::UnexpectedNonce);
    }
    let mut data = Vec::with_capacity(prover_message.len().saturating_add(16));
    data.extend_from_slice(prover_message);
    push_u64(&mut data, kind as u64 | (u64::from(work_bits) << 8) | (call_number << 16));
    push_u64(&mut data, nonce);
    Ok(h(162, label, round, Some(rho_before), &data, None)?
        .try_into()
        .expect("64-byte hash output"))
}

/// Reference chain primitives; not a verifier and does not enforce a proof plan.
#[derive(Debug, Clone)]
pub struct Chain {
    label: u64,
    rho: Digest,
    rounds: u64,
}
impl Chain {
    pub fn new(label: u64, rho0: Digest) -> Result<Self, TranscriptError> {
        valid_label(label)?;
        Ok(Self { label, rho: rho0, rounds: 0 })
    }
    pub fn value(&self) -> &Digest {
        &self.rho
    }
    pub fn rounds(&self) -> u64 {
        self.rounds
    }

    /// Failed proof of work leaves the chain unchanged.
    pub fn close_round(&mut self, message: &[u8], kind: RoundKind, work_bits: u8, nonce: u64) -> Result<Draw, TranscriptError> {
        let round = self.rounds.checked_add(1).ok_or(TranscriptError::RoundOverflow)?;
        let before = self.rho;
        let first = round_call(self.label, round, &before, message, kind, work_bits, nonce, 0)?;
        if work_bits != 0 {
            let word = u64::from_le_bytes(first[..8].try_into().expect("eight bytes"));
            let mask = if work_bits == 64 { u64::MAX } else { (1_u64 << work_bits) - 1 };
            if word & mask != 0 {
                return Err(TranscriptError::WorkNotSatisfied);
            }
        }
        let mut rho = [0_u8; 32];
        if work_bits == 0 {
            rho.copy_from_slice(&first[..32]);
        } else {
            rho.copy_from_slice(&first[32..64]);
        }
        self.rho = rho;
        self.rounds = round;
        Ok(Draw {
            label: self.label,
            round,
            before,
            message: message.to_vec(),
            kind,
            work_bits,
            nonce,
            first,
            words_taken: 0,
        })
    }
}

/// Draws the verifier's message using the exact B_0, B_1, ... ordering.
pub struct Draw {
    label: u64,
    round: u64,
    before: Digest,
    message: Vec<u8>,
    kind: RoundKind,
    work_bits: u8,
    nonce: u64,
    first: [u8; 64],
    words_taken: u64,
}
impl Draw {
    pub fn word(&mut self) -> Result<u64, TranscriptError> {
        let first_block = if self.work_bits == 0 { 1_u64 } else { 2_u64 };
        let block = first_block.checked_add(self.words_taken / 4).ok_or(TranscriptError::TooManyDraws)?;
        let call_number = block / 2;
        let output = if call_number == 0 {
            self.first
        } else {
            round_call(self.label, self.round, &self.before, &self.message, self.kind, self.work_bits, self.nonce, call_number)?
        };
        let offset = (block % 2) as usize * 32 + (self.words_taken % 4) as usize * 8;
        let word = u64::from_le_bytes(output[offset..offset + 8].try_into().expect("eight bytes"));
        self.words_taken = self.words_taken.checked_add(1).ok_or(TranscriptError::TooManyDraws)?;
        Ok(word)
    }
    /// R6.4: a Goldilocks element, with no modulo reduction.
    pub fn base(&mut self) -> Result<Fp, TranscriptError> {
        for _ in 0..6 {
            let word = self.word()?;
            if word < MODULUS {
                return Ok(Fp::from_canonical(word).expect("below modulus"));
            }
        }
        Ok(Fp::ZERO)
    }
    pub fn extension(&mut self) -> Result<Ext3, TranscriptError> {
        Ok(Ext3([self.base()?, self.base()?, self.base()?]))
    }
    pub fn extension_nonzero(&mut self) -> Result<Ext3, TranscriptError> {
        for _ in 0..2 {
            let x = self.extension()?;
            if x != Ext3::ZERO {
                return Ok(x);
            }
        }
        Ok(Ext3::ONE)
    }
    pub fn position(&mut self, width: u8) -> Result<u64, TranscriptError> {
        if width >= 64 {
            return Err(TranscriptError::InvalidPositionWidth(width));
        }
        Ok(self.word()? & ((1_u64 << width) - 1))
    }
    /// 32 trits per 64-bit word; leftover bits are discarded.
    pub fn trits(&mut self, count: usize) -> Result<Vec<i8>, TranscriptError> {
        if count > 16_777_216 {
            return Err(TranscriptError::TooManyDraws);
        }
        let mut out = Vec::with_capacity(count);
        let mut word = 0_u64;
        for i in 0..count {
            if i % 32 == 0 {
                word = self.word()?;
            }
            out.push(match word & 3 {
                1 => 1,
                3 => -1,
                _ => 0,
            });
            word >>= 2;
        }
        Ok(out)
    }
    pub fn seal(&mut self) -> Result<Digest, TranscriptError> {
        let mut value = [0_u8; 32];
        for i in 0..4 {
            value[i * 8..(i + 1) * 8].copy_from_slice(&self.word()?.to_le_bytes());
        }
        Ok(value)
    }
}

#[cfg(test)]
mod tests;
