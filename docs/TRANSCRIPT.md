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

## Real accepted proof: first two consecutive rounds

A separate test-only diagnostic hook in the *pinned upstream C++ checkout*
records the first query's public parameter and statement serialization, its
salt, and the first two rounds after C++ has verified the real accepted proof.
The original C++ verifier's acceptance path is unchanged: hooks only log
values after their ordinary calculations.

The Rust `real_first_round` test binary then:

1. Independently hashes the serialized parameter bytes with H(169,0,1)
   and reconstructs the run value and first-query digest.
2. Reads the 32-byte salt, the first 64-byte `SEND seed` message and the
   next 96-byte `SEND answer` message directly from the **original proof**.
3. Recomputes the exact transcript states rho_0, rho_1 and rho_2.
4. Compares the first three extension-field challenges sampled by C++.
5. Rejects mutations of the salt, each round's bytes, a truncated second
   message, and the parameter serialization (five negative tests).

The verified result was `REAL_FIRST_TWO_ROUNDS_OK`. The test rejects on
disagreement, including under `tee` because the CI step uses `set -euo pipefail`.

Evidence: https://github.com/qoosmo/rust-flashprove/actions/runs/42048102858
The C++ hook must convert its internal `RoundKind` into the wire's
`ChainKind`, e.g. `EMPTY` is 0 internally but 7 on the wire.

This is **not** full verifier equivalence: the initial public parameters
and statement are still serialized by upstream C++ and passed to Rust through
the trace, not constructed from scratch in Rust. Only the first two rounds
are replayed, and no Merkle opening, sub-proof equation or final proof
decision is implemented in Rust.

## Local development

    cargo test -p flashprove-transcript
    cargo run -p flashprove-transcript --bin transcript_rust_oracle

The C++ oracle requires a Linux build with upstream blocks/ and prover/
headers at the pinned commit. See differential-smoke.yml for the exact command.

## Next protocol work

- Serialize real parameters and statement independently from public inputs
  and the request's proof plan, without copying C++ binder bytes.
- Parse subsequent proof rounds including file-only Merkle openings and
  the next two chains; check every nonce, message, and challenge.
- Verify Merkle openings, low-degree/sumcheck equations and key/leaf links.
- Only then compare full acceptance and rejection decisions on a hostile corpus.
