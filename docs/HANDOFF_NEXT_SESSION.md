# RustFlashProve: handoff for the next session

Repository: `qoosmo/rust-flashprove`, branch `feat/d6-native-openings` (draft PR #2, stacked on PR #1
`feat/cpp-rust-differential-smoke`). Last commit of the previous session: `c0567d0`. All CI green.
Pinned upstream: `anthropics/FlashProve` at `9e2bdd8ff5bf9c62f18263d7dac189b0400b260c`.
Lean formalisation is deferred. The public `verify` entry point stays **fail-closed** until every
chain is algebraically verified.

## Working rules (from the owner)

- Rust only for new code; C++ only as test-only instrumentation or oracles of the pinned upstream.
- Precise and direct; no "what we do not claim" framing; incremental validation before claims.
- Every port step ends with its values equal to upstream's (`VerifierContext::notes`).
- Warn before token-heavy work and offer a cheaper option. Reply in English.

## Where things stand

| Stage | Status |
|---|---|
| D6 Merkle openings (first chain) | Done: 20 openings verified natively, 0 unaccounted bytes |
| D8-A whole proof walk | Done: head, 3 chains, place, 35 openings, 4,145,300 bytes, to EOF; cross-chain linkage (seals, binding root, table) checked natively |
| Shared chain algebra (D7+D9 per block) | In progress: **9 of 45 notes** equal upstream (0–7, 26) |
| Second chain | Blocked on the first chain: it reads `LinFirst` (W_c, the request's claim, its group) |
| First chain algebra (model segments) | Not started |

Negative corpus: `scripts/proof_negative.py`, 350 cases; Rust rejects all 348 it must; the clean
`cp_verify` says NO to all 329 proof mutations. Two schedule fields are not bound by Merkle
(`NOT_BOUND_BY_MERKLE`: part split of a column, `log_n_zk`): D7 must derive them, D9 enforce them.

## Read first (in the repo)

1. `docs/SHARED_CHAIN_MAP.md`: rounds 1–42 of the shared chain by block, C++ entry points, the
   three explicit refusals, port order S0–S10 with status, the confirmed claim lists of both groups.
2. `docs/PROOF_WALK.md`, `docs/OPENINGS_AUDIT.md`: what the walk checks and what is not native.
3. `tests/vectors/README.md`: every committed vector and how it is regenerated.

## Code map

- `crates/flashprove-merkle`: shapes, position lists, leaf/vertex hashes, walk, per-root record (R7).
- `crates/flashprove-walk`: `walk_proof` (whole file), `ChainWalk` keeps each round's `Draw`
  (positioned after positions/seal; invariant: one per round) and each opening's columns and
  draw order. Binaries: `proof_walk`, `shared_chain_check`.
- `crates/flashprove-iop`: `code` (RS codes, points z_I, factors), `shapes` (Codes, LinShape,
  FoldeqShape, IoppStage; canonical parse + faults), `ext` (eq tables, inner products),
  `foldeq` (table item/record, weights, Rec/Col targets, generator rows), `lin` (Fold row
  coefficients), `claims` (group claim targets in `begin_run` order, BAT target, SPLIT targets).

## Next step: S2 coefficient side, then FOLD

Goal: reproduce notes 8 (FOLD target, test_u) and onward. Needed:

1. Port `Row` (relation.h): terms, units, runs, `MainForm` with `Tensor`/`Form` (tensor.h:
   `Tensor::eq`, `product`, `push`, picks, `tensor_below`, `insert_choice`), `VectorLay::on_table`
   / `index` (foldeq.h), oracle parts (MAIN, MASK) and `GroupLayout` (`main_first`, `k`, kept).
2. Port `add_to_group_row` (relation.h:651) and `Bat::combine` coefficients (bat.h) so the BAT
   `GroupRow` has its coefficient vector `c`, not only its target.
3. Port the FOLD start and rounds (`fold.h`: `fold_start_verify` :444, `fold_rounds_verify` :462;
   `fold_rounds.h`): kind-2 round's hiding sum last (R8.4), sumcheck-style round polynomials.
4. Then CS (`cs.h:721`), then BASE (`base_case.h:196`): the two refusals
   `<c, M'> = t* + λ t` and "encoding equals opened symbols". Only after BASE can a bad proof be
   rejected algebraically.

Each step: add the new values to `shared_chain_check` (explicit upstream note index), bump the
CI line `cpp_notes_compared=N of 45`, add negative cases on the algebraic bytes.

## Commands

```bash
# Upstream (read-only) and a test-only instrumented worktree
GIT_LFS_SKIP_SMUDGE=1 git clone https://github.com/anthropics/flashprove upstream && git -C upstream checkout 9e2bdd8ff5bf9c62f18263d7dac189b0400b260c && (cd upstream && verifier/build.sh) && git -C upstream worktree add ../upstream-instr 9e2bdd8ff5bf9c62f18263d7dac189b0400b260c && python3 scripts/instrument_upstream_openings.py ../upstream-instr && python3 scripts/instrument_upstream_all_chains.py ../upstream-instr && python3 scripts/instrument_upstream_notes.py ../upstream-instr && (cd ../upstream-instr && verifier/build.sh)

# Diagnostics: one log per stage process (<prefix>.<pid>); the request stage holds chain 46524d01
F=upstream/examples/accepted-proof; mkdir -p reports/logs && RUSTFLASH_NOTES_LOG=$PWD/reports/logs/notes RUSTFLASH_CHAINS_LOG=$PWD/reports/logs/chains RUSTFLASH_OPENINGS_LOG=$PWD/reports/logs/openings ../upstream-instr/bin/cp_verify $F/config $F/ivk $F/example.req $F/example.y $F/example.proof -id "$(cat $F/ID.txt)" -q && pid=$(grep -l '^chain label=46524d01 ' reports/logs/chains.* | sed 's/.*\.//') && python3 scripts/extract_proof_inputs.py reports/logs/chains.$pid reports/logs/openings.$pid $F/example.proof reports/inputs

# Native walk and shared-chain values, compared with upstream afterwards
cargo build --release -p flashprove-walk && ./target/release/proof_walk $F/example.proof $F/example.req $F/config/policy.txt $F/config/layout.txt $F/config/KL.bin reports/inputs tests/vectors/accepted-proof.proof.schedule && ./target/release/shared_chain_check $F/example.proof $F/example.req $F/config/policy.txt $F/config/layout.txt $F/config/KL.bin reports/inputs tests/vectors/accepted-proof.proof.schedule --compare-notes tests/vectors/accepted-proof.notes.txt
```

## Pitfalls met

- rustfmt reflows code: a Python string replacement that misses leaves code unchanged silently.
  Assert each anchor (`assert old in s`) before replacing.
- `cargo fmt --all` reformats the old transcript crate; format only the new crates' files.
- Instrumented logs: stage processes write concurrently; logs are per process (`<prefix>.<pid>`).
- Draws: a protocol block continues the round's `Draw` after its positions (CS draws its batching
  element after positions); take draws only through `ChainWalk::draw(k)`.
- Do not run commands chained with `&&` after a `grep` that may match nothing.

## Estimates (honest)

Shared chain S2–S10: about 2,500 verifier-side C++ lines; several sessions. Then the first chain
(model segments: layers, attention, lookups, smallness), the second chain, the key and leaf stages
(table authenticity), the verdict and API, and the release. Realistic total before Lean: months.
