//! Fail-closed verifier API. No cryptographic verification is implemented yet.

use flashprove_format::{FormatError, Request};

#[derive(Debug, PartialEq, Eq)]
pub enum VerificationError {
    MalformedInput(FormatError),
    NotImplemented,
}

impl std::fmt::Display for VerificationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MalformedInput(e) => write!(f, "malformed input: {e}"),
            Self::NotImplemented => write!(f, "verifier is not implemented; no acceptance verdict"),
        }
    }
}
impl std::error::Error for VerificationError {}

/// Parses the envelope then returns NOT IMPLEMENTED: passing this function never means ACCEPT.
pub fn verify(
    proof_bytes: &[u8],
    request_bytes: &[u8],
    y_bytes: &[u8],
) -> Result<(), VerificationError> {
    flashprove_format::parse_proof(proof_bytes).map_err(VerificationError::MalformedInput)?;
    let request =
        Request::parse(request_bytes, 1_000_000).map_err(VerificationError::MalformedInput)?;
    request
        .validate_window()
        .map_err(VerificationError::MalformedInput)?;
    let y =
        flashprove_format::parse_next_token(y_bytes).map_err(VerificationError::MalformedInput)?;
    request
        .validate_next_token(y)
        .map_err(VerificationError::MalformedInput)?;
    Err(VerificationError::NotImplemented)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn valid_header_can_never_accept() {
        let proof = b"CPPFH821\0\0\0\0";
        let req: Vec<u8> = [1_u32, 0, 1].iter().flat_map(|x| x.to_le_bytes()).collect();
        assert_eq!(
            verify(proof, &req, &0_u32.to_le_bytes()),
            Err(VerificationError::NotImplemented)
        );
    }
}
