# Upstream verifier map — pinned 2026-11-05

Commit: `9e2bdd8ff5bf9c62f18263d7dac189b0400b260c`.

| Question | Source of truth | Finding / Rust action |
|---|---|---|
| Main entry | `verifier/src/cp_verify.cpp` | `cp_verify`, three child-process stages key/leaf/request |
| Build | `verifier/build.sh` | C++ requires Linux, g++ 13+ for normal route |
| Binary headers | `verifier/src/vf_input_files.h`, `blocks/frame/heads.h` | `CPIK`, `CPEN` 8-byte headers; `CPPF` 12-byte header; H821 |
| Byte-level specification | `docs/format/FORMAT.md` | Rule R1.1 little-endian u64, R1.3 canonical F, R14.x proof |
| Whole proof walkthrough | `docs/format/read_proof.py` | Spec-based diagnostic walker (not a verifier) |
| Full proof body | `docs/format/10-proof-file.md` | Three chains with dynamic round plan; no stored file length |
| Request and y | `verifier/README.md`, `docs/format/FORMAT.md` section 12 | `T` x u32 LE + `r,e`; y one u32 LE |
| Policy / params | `verifier/docs/parameter-file.md`, `blocks/frame/parameters.h` | text begins `version H821`; config also includes KL.bin/layout.txt |
| Field | `verifier/src/vf_common.h`, format R1.2–R1.4 | Goldilocks p, cubic extension E=F[X]/(X^3-2) |
| Fiat-Shamir | `verifier/src/vf_transcript_channel.h`, `blocks/chain/rounds.h` | planned rounds, canonical reads, transcript challenges |
| Hash / commitment | `blocks/hash/`, `blocks/iop/`, `blocks/frame/check*.h` | BLAKE2b + domain separation / Merkle + opening checks |
| Lean soundness | `lean/THEOREM.md` | theorem targets Lean protocol verifier, NOT cp_verify |
| Lean C++ translation | `lean/OnBytes/Main.lean` | `programFront`, hand translation; no standalone executable shipped |
| Lean exercise/test route | `lean/Ask/`, `tools/accepts/` | exact invocation to be audited for differential corpus |
| Upstream test corpus | `verifier/tests/`, `examples/accepted-proof/` | stored accepted proof, many hostile-file regressions |
| Output contract | `verifier/docs/output.md` | C++ YES=0, NO=1, NOT CHECKED=5, NOT-A-VERIFICATION=14 |

## First Rust library boundaries

- `flashprove-field` — canonical representation, arithmetic + extension encoding (implemented)
- `flashprove-format` — checked cursor, header and request parsing (implemented, incomplete for proof body)
- `flashprove-verifier` — explicit NotImplemented error (implemented)
- `flashprove-cli` — inspection and fail-closed interface (implemented)
- `flashprove-transcript`, `flashprove-commitment` — planned after exact upstream vectors

## Open verifier map items

- Exact wire plan for example.proof, including round counts, challenges and openings.
- Full validation of policy.txt, KL.bin, layout.txt against cp_verify.
- Differential harness that actually executes C++, Lean and Rust on a common corpus.
- Necessary hash domain constants and first query construction.
- Proved relation between Rust operations and Lean functions / compiled semantics.
