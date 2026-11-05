# RustFlashProve

**Independent Rust implementation of FlashProve's verifier interface — work in progress.**

This project studies the gap between Anthropic's formally specified protocol / Lean verifiers
and its optimized C++ verifier. It begins with strict, auditable parsing and reference
arithmetic, then proceeds to transcript and commitment checks and differential validation.

> **Current safety status:** The Rust executable is **not a verifier yet**. It can inspect
> some files but cannot validate proofs. `flashprove verify` always fails closed with exit code 5.
> It does not print YES or ACCEPT. It must not be used for security decisions.

Upstream: [anthropics/FlashProve](https://github.com/anthropics/FlashProve)
(pinned at `9e2bdd8ff5bf9c62f18263d7dac189b0400b260c`, FlashProve 0.16.0).
Independent repository; no Anthropic affiliation.

## What's implemented

- `flashprove-field`: Goldilocks `Fp` (modulus `2^64 - 2^32 + 1`) and cubic `Ext3 = Fp[X]/(X^3-2)`.
  Straightforward reference arithmetic, not optimized or constant-time.
- `flashprove-transcript`: H821 BLAKE2b domain hashes, first queries, Fiat–Shamir
  rounds, proof-of-work and challenge draws. Tested against upstream published vectors
  and the original C++ Chain implementation on a deterministic transcript.
- `flashprove-format`: bounded, checked byte cursor, canonical field decoding, strict `H821`
  proof/key/leaf headers, typed proof envelope (opaque unverified body), request and next-token
  files (little-endian `u32`), initial policy version check.
- `flashprove-verifier`: deliberately fail-closed entry point (unimplemented cryptographic checks).
- `flashprove-cli`: inspection-only commands, plus explicitly unsupported `verify` command.
- Two **exact upstream binary regression fixtures**, recovered from the pinned release.

The binary proof file **has no length prefix**. Only the twelve-byte header is parsed at this
stage; the proof body is not traversed, as decoding requires a planned chain of rounds.

## Commands

Prerequisite: Rust stable (>= 1.82).

```sh
cargo fmt --all  # normalize bootstrap sources, then check
cargo fmt --all -- --check
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace
cargo run -p flashprove-cli -- inspect-request \
  tests/vectors/upstream-example.req tests/vectors/upstream-example.y
cargo run -p flashprove-cli -- inspect-proof path/to/example.proof
```

Expected output of the request inspection includes `T=64 r=60 e=64 next_token=199` and
`NOT VERIFIED`. To use upstream's full reference verifier, see its own README: it needs
five file paths plus an independently trusted commitment ID (`-id`). This Rust tool does not
replace that check.

## Structure

```text
crates/
  flashprove-field/       Reference arithmetic + canonical encodings
  flashprove-format/      Checked reads, headers, request + token files
  flashprove-transcript/  Byte-exact H821 hash chain and challenge sampler
  flashprove-verifier/    Fail-closed verifier API; no proof acceptance
  flashprove-cli/         Inspection tool

tests/vectors/            Pinned upstream small binary fixtures
upstream/                 Exact upstream revision

docs/ARCHITECTURE.md      Trust boundaries and scope
docs/TRANSCRIPT.md        C++/Rust transcript compatibility evidence

docs/VERIFIER_MAP.md      Grounded upstream mapping

docs/MILESTONE.md         Evidence, limitations, next stages
scripts/RUN.sh            Run formatting, linting, tests
scripts/PUBLISH_TO_GITHUB.sh   Opt-in publication from a local machine with gh
```

## Research roadmap

```text
Actual upstream H821 bytes → typed Rust file inputs (in progress)
    ↓
Reference transcript and challenge draws (tested; real-proof integration open)
    ↓
Merkle/opening/lookup/IOP checks → complete Rust verifier (open)
    ↓
Common valid + hostile corpus against C++ (open)
    ↓
Compare to the right Lean executable / formal spec (open)
    ↓
Prove selected correspondence lemmas (open)
```

See [docs/MILESTONE.md](docs/MILESTONE.md) for verified vs. planned functionality.

## Attribution and status

Apache-2.0, see [`LICENSE`](LICENSE), [`NOTICE`](NOTICE), and
[`upstream/UPSTREAM.md`](upstream/UPSTREAM.md). The protocol/format and test fixtures originate
from Anthropic's open source research artifact. Rust crate source was written independently.
No production readiness, soundness claim, equivalence proof, or security audit is implied.
