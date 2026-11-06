# Shared chain (`FRM\x03`): algebraic verification map (stages D7 + D9)

Pinned upstream `9e2bdd8ff5bf9c62f18263d7dac189b0400b260c`. Target: verify the shared chain of the
accepted proof **algebraically** in Rust, block by block, with each block's shapes (D7) and checks
(D9) ported together.

## Why the shared chain first, and not the second

- The shared chain depends on the first chain only through the binding root (`lin_bind_shared`),
  which `proof_walk` already derives natively. Its checks read the table (stored opening), its own
  oracles and its own draws.
- The second chain is **not** self-contained: `lin_second_verify` takes `LinFirst` (the first
  chain's W_c oracle, the request's claim and its group `first.own`, `blocks/iop/lin.h`), and its
  proximity test reads rows that the first chain's segment checks added to that group. It can be
  verified only after the first chain (model segments). This corrects the earlier plan.

## Entry points (`blocks/frame/check.h`, `check_proof`)

```text
lin_shared_verify(shared_V, shared_x, TableTest::LATER, tested, shared)      lin.h:738 -> :522
lin_shared_tests_verify(shared_V, shared_x, shared)                          lin.h:749 -> :566
shared_ch.seal(R_SEAL) && finish_inside_a_file()
```

## Rounds of the accepted proof's shared chain, by block

| Rounds | Names | Block (C++) | What is read |
|---|---|---|---|
| 1 | LIN point | `lin_draw` (lin.h) | draws psi ∈ E^{k_col} |
| 2–3 | SEND seed, SEND answer | `foldeq_verify` → `send_verify` (foldeq.h:834, send.h:560) | root of G_u (tree 0); sample answers |
| 4 | LOC (+ stored opening) | `foldeq_columns_verify` (foldeq.h:744), `IndexKey::read` | the table's columns at 53 positions |
| 5–6 | SEND seed, SEND answer | `send_verify` (lin_message_omega) | roots of Omega and the split mask (trees 1, 2); answers |
| 7 | LIN zeta | `lin_draw` | zeta ∈ E^{k_row} |
| 8 | SPLIT | `split_verify` (split.h:113) | one element |
| 9–26 | BAT, FOLD ε, 5×FOLD round, SEND seed, CS, FOLD ε, 4×FOLD round, SEND seed, CS, BASE λ, BASE | `iopp_verify(group_u, test_u)` (iopp.h:256): `bat_verify` (bat.h:139), `fold_start_verify`/`fold_rounds_verify` (fold.h:444/462), `cs_verify` (cs.h:721), `base_verify` (base_case.h:196) | stage roots (trees 3, 4); CS openings of trees 0, 2 then 3; BASE codeword (76,992 bytes), opening of tree 4 |
| 27–41 | BAT, FOLD ε (+root tree 5), 2×FOLD round, SEND seed, CS, FOLD ε, 4×FOLD round, SEND seed, CS, BASE λ, BASE | `iopp_verify(group_omega, test_omega)` (split needed) | trees 5, 6, 7; CS openings of trees 1, 2, 5 then 6; BASE codeword (126,144 bytes), opening of tree 7 |
| 42 | SEAL | `Rounds::seal` | — (native since D8) |

## Differential checkpoints (upstream `VerifierContext::notes`)

`scripts/instrument_upstream_notes.py` turns on upstream's own block-by-block notes ("for comparing a
second implementation of the verifier block by block"). The accepted proof's shared chain has **45**
notes, in this order; the Rust port must reproduce each value exactly:

```text
 0 FOLDEQ: e_0                      5 LIN: (Fold) on Omega<0>
 1 FOLDEQ: (Rec_0)'s target         6 LIN: (Fold) on G_u<1>
 2 FOLDEQ: (Col_1)'s target         test_u:  7 BAT target, 8 FOLD target, 9-15 CS (y_main, y_0, y_1,
 3 FOLDEQ: (Col_1) on G_u<0>                 target, c'[0], d'[0], d's last), 16 FOLD, 17-23 CS,
 4 FOLDEQ: (Col_1) on G_u<B>                 24-25 BASE left / right
                                    test_omega: 26 BAT, 27 FOLD, 28-34 CS, 35 FOLD, 36-42 CS,
                                                43-44 BASE left / right
```

The second chain has 21 (LIN (Dot), then one test), the first chain 68.

## Where a proof is rejected

Explicit refusals in this call graph are only three; everything else reduces to linear claims whose
targets each block computes, so **soundness depends on computing every row exactly**:

1. `foldeq.h`: the table's opened columns do not lead to its root (native since D8).
2. `base_case.h`: the encoding of the masked message differs from the opened symbols at a listed
   position.
3. `base_case.h`: the masked message does not satisfy the linear claim
   `<c, M'> = target* + λ·target`.

Implicit rejections, all to be ported: a missing or non-canonical element (`VerifierRounds::take`,
R8.8: every element of every message is tested), a missing root or opening (native), proof of work
(native), and `Statement` invariants that the reference enforces with `BLK_REQUIRE` (the program's
own faults, ported as `debug_assert` + fail-closed errors).

## Port order (each step ends with its checkpoints equal to C++)

| Step | Rust module (`flashprove-iop`) | C++ | Checkpoints |
|---|---|---|---|
| S0 ✔ | `code`: codes, points, factors | code.h, cosets.h | 48 points equal upstream `gl64_point` |
| S0 ✔ | `shapes`: Codes, LinShape, FoldeqShape, IoppStage | lin.h, foldeq.h, iopp.h, context.h | bound bytes round-trip; faults |
| S1 ✔ | `ext`: E arithmetic, inner products, eq tables, products | field.h, mle.h, tensor.h (eq parts) | via notes 0–6 |
| S2 ◐ | `claims`: groups' claim targets in `begin_run` order (PLAIN as added, samples by member as sent, GENERATOR as added), once-only test ✔; `tensor`: Tensor, Form, frozen parts ✔; `relation`: Row, Run, Statement (verifier), GroupLayout, `add_to_group_row`, `VectorLay` ✔ (semantics in `docs/PORT_NOTES.md`) | relation.h, tensor.h | via notes 7, 26 ✔; coefficient side by unit tests against written-out vectors |
| S3 ◐ | `send`: cube, pads, sample claim form, `admit_all` ✔; seeds from draws and `vector_room` pending | send.h, foldeq.h | form against its definition (unit test) |
| S4 ◐ | `foldeq`: record parse, weights, (Rec) targets, (Col) symbols, generator row ✔; record seeds and the full rows wait for S2 | foldeq.h | notes 0–4 ✔ |
| S5 ◐ | `lin`: lin_fold_row coefficients ✔; SPLIT targets ($s$, $t-s$) ✔; the halves' coefficients wait for S2 | lin.h, split.h | notes 5–6 ✔ |
| S6 ◐ | `bat`: batch target ✔; `bat::combine` (coefficients, via `add_to_group_row`) ✔, fed once SEND's sample rows (S3) and FOLDEQ's/LIN's full rows exist | bat.h | notes 7, 26 ✔ |
| S7 ◐ | `fold`: running claim ✔, `fold_output` (c fixed and frozen, kept factor, mask form, mask weights), shape and row checks ✔ | fold.h, fold_rounds.h, fold_algebra.h | notes 8, 27 ✔; 16, 35 follow CS |
| S8 ◐ | `cs`: single rows' symbols at the first draw ✔; next group's claims (`switch_rows`) pending | cs.h, single_rows.h | notes 9–11, 28–30 ✔; 12–15, 31–34 need the claims' coefficients |
| S9 | `base`: BASE checks (the two refusals) | base_case.h | notes 24–25, 43–44 |
| S10 | integrate into `proof_walk` → `shared_chain_verified` | iopp.h, lin.h | all 45; negative corpus on algebraic bytes |

Progress: `shared_chain_check` reproduces notes 0–11 and 26–30 (17 of 45) from the native walk's own draws and
openings, compared with upstream in CI. Each round's verifier message is kept as a `Draw` positioned
after its positions, so later blocks draw in the reference's order (an invariant: one draw per round).

S1–S10 are about 2,500 verifier-side C++ lines (of ~4,600 in these files with the prover's). Only
after S10 does the walk report the shared chain as **algebraically verified**; `verify` stays
fail-closed until every chain is.

### Confirmed by the notes: the claims of the two groups

- G_u's group, in `begin_run` order: (Rec_0..Rec_{A-1}) [PLAIN], LIN (Fold) second share with target
  $-s$ [PLAIN], G_u's sample answers (round 3), the shared split mask's answers (round 6, after
  Omega's) [SAMPLE], then one (Col) per **draw** of the LOC round, repeats included [GENERATOR].
- Omega's group: LIN (Fold) first share with target $s$ [PLAIN], Omega's answers, the split mask's
  answers [SAMPLE].
- $s$: the one element of the SPLIT round (round 8); (Fold) has target 0.
