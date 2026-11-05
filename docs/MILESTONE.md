# Stage A/B/C evidence snapshot — 2026-11-05

## PROVED / VERIFIED

- Upstream public commit pin was read via the GitHub API:
  `9e2bdd8ff5bf9c62f18263d7dac189b0400b260c`.
- Headers, field and binary request format are grounded in upstream source and FORMAT.md.
- The included request and next-token fixtures are *byte-identical to upstream*:
  - `upstream-example.req`: 264 bytes, SHA-256 `ce700974a03d43586d66ca742f9bbc8ad45c936d03dfdb8614dd559a2780aa13`.
  - `upstream-example.y`: 4 bytes, SHA-256 `add7f2a4843f8c512c0e2875546581db11b9ba227ee008b5f719dfacb125de76`.
- A Python cross-check of the fixture bytes recovered `T=64, r=60, e=64, y=199`.
- No Rust compilation or Rust tests have been run in the authoring container (Rust toolchain absent).

## IMPLEMENTED (source written; compilation still to be performed)

- Four-crate Cargo workspace and GitHub Actions workflow.
- Canonical field and 3-coordinate extension-field encoding and arithmetic.
- Bounds-checked byte cursor; proof / key / leaf headers.
- Strict request and next-token file readers, optional semantic window checks.
- Explicit `NotImplemented` instead of any proof acceptance.
- Unit tests: boundary, field arithmetic, extension, malformed headers, upstream fixture.

## TESTED

- Upstream binary-fixture SHA-256 and structural parameters checked in Python, exact matches.
- **No `cargo test` claim:** the container has neither cargo nor rustc.
- **No C++ or Lean execution claim:** their binaries were not built locally.

## OPEN

1. Complete proof-body parser from an exact dynamic round plan.
2. Strict configuration validation and hashing, transcript state + BLAKE2b.
3. Commitment, Merkle, sumcheck, lookup and full verifier orchestration.
4. Actual C++↔Rust↔Lean differential harness, including negative tests.
5. Formal correspondence proof; soundness theorem assumptions.

## NEXT

- On a machine with Rust: `bash scripts/RUN.sh`; fix any compilation or lint findings.
- Obtain/clone pinned upstream and use its stored `example.proof` as the first body-walk target.
- Add a trace interface for planned rounds (read elements, close round, challenge bytes),
  initially with upstream vectors; implement nothing by guessed format.
- Add differential tests with definitive outcomes and explicit input domain.

### Note on GitHub publication

The `qoosmo/rust-flashprove` repository was not found via the connected GitHub tool.
Repository creation is not exposed through this connection and no publication occurred.
The opt-in script `scripts/PUBLISH_TO_GITHUB.sh` prepares local publication with GitHub CLI.
