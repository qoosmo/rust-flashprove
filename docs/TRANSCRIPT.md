# H821 Fiat-Shamir transcript: C++ / Rust differential

Upstream pin: 9e2bdd8ff5bf9c62f18263d7dac189b0400b260c.

## Implemented component

The flashprove-transcript crate implements the byte-level rules in upstream
docs/format/FORMAT.md (R2.1-R2.3, R4.5-R4.6, R5.2-R5.5, R6.1-R6.9):

1. H(number, tree, index, start; bytes): BLAKE2b with a 16-byte LE label,
   32-byte salt/personalization taken from start when the domain requires it,
   256-bit output except for the 512-bit round-query domain 162.
2. Run and first-query states for an empty record field.
3. Round queries C_i(j), including the nonce, the challenge kind,
   work bits, call index and previous transcript value.
4. Proof-of-work checks (0 to 64 bits); failure leaves the state unchanged.
5. Goldilocks field-2 challenge sampling: six attempts, no modulo reduction;
   cubic extension challenges, nonzero challenges, positions, trits and seals.

This is independent Rust reference code, not a Rust proof verifier.

## Evidence

- Unit tests pin byte-exact H outputs and the published six-round field-2
  transcript, including the 8-bit proof-of-work nonce 116, two challenge
  kinds, positions, seed points, factor, trits, and seal.
- scripts/transcript_cpp_oracle.cpp invokes the original
  blocks/chain/chain.h C++ implementation on a deterministic four-round
  protocol (H821 field 2).
- crates/flashprove-transcript/src/bin/transcript_rust_oracle.rs independently
  constructs the same transcript and prints the same named states/draws.
- Both oracles also hash the real accepted-proof public configuration files
  (policy.txt, layout.txt and KL.bin) via R4.9; the resulting configuration
  digest must match byte-for-byte before their synthetic transcript outputs.
- GitHub Actions compiles both oracles on Linux and runs diff -u over their
  entire output, failing if any state or element differs.
- The separate differential_smoke.py compares whole C++ proof decisions against
  Rust structural file inspection; its known mismatches in semantic coverage
  are recorded honestly.

Successful oracle equality is component-level differential evidence, not
end-to-end verifier equivalence or a mathematical proof of equivalence.

## Local development

    cargo test -p flashprove-transcript
    cargo run -p flashprove-transcript --bin transcript_rust_oracle

The C++ oracle requires a Linux build with upstream blocks/ and prover/
headers at the pinned commit. See differential-smoke.yml for the exact command.

## Next protocol work

- Derive the real parameters' digest and request-stage first query from the
  public configuration and accepted proof.
- Parse the complete statement-dependent proof-body plan, and feed every
  message/nonce into the transcript in exact order.
- Compare the C++ and Rust challenge trace of the real accepted proof (not
  merely a synthetic transcript).
- Verify Merkle openings, low-degree/sumcheck equations and key/leaf links.
- Only then compare full acceptance and rejection decisions on a hostile corpus.
