# RustFlashProve — verified milestone snapshot (2026-11-05)

## Upstream and repository

- Reference: Anthropic FlashProve `9e2bdd8ff5bf9c62f18263d7dac189b0400b260c`.
- Public Rust repository: https://github.com/qoosmo/rust-flashprove.
- New implementation under draft PR #1, not merged to `main`.
- Rust workspace builds and tests in Linux GitHub Actions; this authoring
  container does not have a Rust toolchain. The prior bootstrap-only status
  is obsolete.

## IMPLEMENTED AND TESTED

1. Goldilocks prime/cubic-extension arithmetic, canonical binary parsing,
   proof-header and request/next-token envelope inspection.
2. H821 BLAKE2b domain-separated hashes, run/first-query values, round calls,
   proof-of-work, and challenge sampling with Anthropic known-answer vectors.
3. Independent C++/Rust synthetic transcript comparison, exact byte equality.
4. Real public configuration digest equality (policy, layout, scales).
5. Strict parser of C++-serialized first-chain round plan and statement, with
   Rust recomputation of its parameter hash, real configuration digest,
   request bytes, and stored-copy index. The fixture has 8,037 plan entries,
   exactly 8,037 expanded physical rounds and 8 named public parameter items.
6. Trace-guided, byte-for-byte reconstruction of **all 8,037 first-chain
   prover messages**, their work nonces and resulting Fiat–Shamir states from
   the accepted proof file. The trace supplies the C++ Reader's observed
   proof offsets; Rust re-reads those bytes independently and recomputes each
   hash and state. This is component-level differential testing, NOT proof
   verification.
7. First two real rounds additionally reproduce three sampled extension
   field challenges. Five first-two-round negative cases, six public-input
   binding negative cases and four bulk-state/offset mutation cases fail
   closed in CI. The separate C++ proof-verdict vs Rust *structural* smoke
   classifies six cases without incorrectly calling structural inspection a
   full verification verdict.

CI evidence:
- All first-chain states: https://github.com/qoosmo/rust-flashprove/actions/runs/42064122802
- First 512 rounds: https://github.com/qoosmo/rust-flashprove/actions/runs/42063607185
- Public-input audit: https://github.com/qoosmo/rust-flashprove/actions/runs/42062180232

## EXACT UNVERIFIED BOUNDARY

- The full first-chain replay SKIPS 2,679,688 bytes of file-only data
  between transcript reads. They may contain Merkle openings and related
  records: **their contents are not verified or parsed in Rust**.
- First-query public parameters/statement and per-field read offsets are
  still serialized/observed by instrumented C++, NOT constructed from scratch
  by Rust. The Rust test independently checks their encoding and external
  bindings, but must not trust this diagnostic as a standalone verifier.
- Shared and second proof chains, algebraic/sumcheck/lookup equations,
  Merkle membership, key and leaf checks, exact end-of-file verification,
  and final YES/NO acceptance by Rust remain unimplemented.
- `flashprove verify` still fails closed. No Lean certification or
  universal semantic-equivalence theorem is claimed.
- This is an exact finite fixture differential, not a security audit.

## NEXT

1. Enumerate and type the skipped file-only ranges, then verify authentic
   Merkle openings and require exact read boundaries in Rust.
2. Build the public first query *independently* from public config, models
   and request plan rather than relying on C++ Binder serialization.
3. Replay the shared and second chains and all drawn challenges.
4. Implement algebraic consistency checks and the full fail-closed Rust
   verifier; only then compare C++/Rust proof acceptance decisions on
   valid and mutated corpora.
5. Certify the correspondence of individual definitions and invariants in Lean.

Implementation and evidence details: `docs/TRANSCRIPT.md`,
`docs/DIFFERENTIAL.md` and `docs/PUBLIC_INPUT_AUDIT.md`.
