# RustFlashProve: handoff for the next session

Repository: `qoosmo/rust-flashprove`, branch `feat/d6-native-openings` (draft PR #2, stacked on PR #1
`feat/cpp-rust-differential-smoke`). Last commit of the previous session: `ee43001`. All CI green.
Pinned upstream: `anthropics/FlashProve` at `9e2bdd8ff5bf9c62f18263d7dac189b0400b260c`.
Lean formalisation is deferred. The public `verify` entry point stays **fail-closed** until every
chain is algebraically verified.

## Working rules (from the owner)

- Rust only for new code; C++ only as test-only instrumentation or oracles of the pinned upstream.
- Precise and direct; no "what we do not claim" framing; incremental validation before claims.
- Every port step ends with its values equal to upstream's (`VerifierContext::notes`).
- Warn before token-heavy work and offer a cheaper option. Reply in English.
- Read `docs/PORT_NOTES.md` before any upstream header: it records the semantics already ported.

## Where things stand

| Stage | Status |
|---|---|
| D6 Merkle openings, D8-A whole proof walk | Done (35 openings, 4,145,300 bytes to EOF, cross-chain linkage) |
| Shared chain algebra (D7 + D9) | **Done: 45 of 45 notes equal upstream; both BASE refusals pass**; `proof_walk` prints `SHARED_CHAIN_VERIFIED notes=45` |
| First chain (request: model segments) | Not started: 68 notes, 8,037 rounds |
| Second chain | Blocked on the first (reads `LinFirst`): 21 notes |

Negative corpus: 350 cases, 0 failures. Two schedule fields are not bound by Merkle
(`NOT_BOUND_BY_MERKLE`); for the shared chain, `flashprove_iop::book` now derives tree shapes, so a
cross-check of the schedule against the book would close them there.

## Code map (new this session)

- `flashprove-iop`: `tensor` (Tensor, Form, frozen parts, `tensor_below`), `relation` (Row, Run,
  Statement, GroupLayout, `add_to_group_row`, VectorLay), `bat`, `fold`, `send`, `split`, `cs`
  (`switch_rows`, no kept members), `book` (`lay_trees`, `TreeBook::enter`, places), plus row
  builders in `foldeq` (`record_row`, `column_row`) and `lin` (`fold_row`).
- `flashprove-walk::shared_chain::shared_chain_notes`: the shared chain driver (library). Binaries
  `shared_chain_check` (compares the 45 notes) and `proof_walk` both call it.

## Next step: the first chain

Scope measured at the end of the session:
- Rounds: PSC round 5,237, PSC epsilon/values/Y 747/736/736, LINE 388, FOLD round 51, BAT-sigma 25,
  SEND 33, ZERO 17, JOIN 14, LKP 20, RNG 5, LOC 5, CS 4, BASE 2, REPLY 1.
- Notes (68): five REQ groups ("the group row's target", "FOLD's target", CS symbols), then one
  IOPP like the shared chain's (BAT, FOLD, CS ×4, BASE). Everything after REQ reuses this
  session's port.
- C++: `verifier/src/cp_verify.cpp` `runStage` (:1264–2557) and `vf_*.h` (~9,300 lines with
  `cp_verify.cpp`), `blocks/iop/{req,req_rows,req_arrays,psc,psc_rows,link,rng,line}.h` (~2,600).
  Estimated 5,000–7,000 verifier-side lines: several sessions.
- Suggested order: (1) `psc.h` + `psc_rows.h` (the sumcheck rounds: most rounds), (2) `req.h`
  groups and their targets (REQ notes), (3) `link.h`, `line.h`, `rng.h`, (4) `vf_*` segment
  checks (attention, lookups, smallness), (5) the final IOPP via `shared_chain`'s loop
  (generalise `run_test` out of the driver first).

## Commands

```bash
# Upstream (read-only), build, test-only instrumented worktree
GIT_LFS_SKIP_SMUDGE=1 git clone https://github.com/anthropics/flashprove upstream && git -C upstream checkout 9e2bdd8ff5bf9c62f18263d7dac189b0400b260c && (cd upstream && verifier/build.sh) && git -C upstream worktree add ../upstream-instr 9e2bdd8ff5bf9c62f18263d7dac189b0400b260c && python3 scripts/instrument_upstream_openings.py ../upstream-instr && python3 scripts/instrument_upstream_all_chains.py ../upstream-instr && python3 scripts/instrument_upstream_notes.py ../upstream-instr && (cd ../upstream-instr && verifier/build.sh)

# Logs and inputs (the request stage holds chain 46524d01)
F=upstream/examples/accepted-proof; mkdir -p reports/logs && RUSTFLASH_NOTES_LOG=$PWD/reports/logs/notes RUSTFLASH_CHAINS_LOG=$PWD/reports/logs/chains RUSTFLASH_OPENINGS_LOG=$PWD/reports/logs/openings ../upstream-instr/bin/cp_verify $F/config $F/ivk $F/example.req $F/example.y $F/example.proof -id "$(cat $F/ID.txt)" -q && pid=$(grep -l '^chain label=46524d01 ' reports/logs/chains.* | sed 's/.*\.//') && python3 scripts/extract_proof_inputs.py reports/logs/chains.$pid reports/logs/openings.$pid $F/example.proof reports/inputs

# Walk + shared chain, compared with upstream
cargo build --release -p flashprove-walk && ./target/release/proof_walk $F/example.proof $F/example.req $F/config/policy.txt $F/config/layout.txt $F/config/KL.bin reports/inputs tests/vectors/accepted-proof.proof.schedule && ./target/release/shared_chain_check $F/example.proof $F/example.req $F/config/policy.txt $F/config/layout.txt $F/config/KL.bin reports/inputs tests/vectors/accepted-proof.proof.schedule --compare-notes tests/vectors/accepted-proof.notes.txt
```

## Pitfalls met

- A tree is read at `x mod 2^{log_n(tree)}`, but a mask-only part riding in a longer tree is read at
  that tree's position (the leaf holds the mask row at `x mod 2^{log_n_zk}`).
- FOLD's round count is the **stage's** k (`iopp_fold_shape` overrides the layout's).
- The FOLD ε message ends with the hiding sum; before it comes the fresh mask's root when the mask
  was not sent ahead.
- rustfmt reflows code: assert each anchor before a scripted replacement; format only new files.
- Byte flips in the proof change every later Fiat–Shamir draw: they cannot test BASE alone.
