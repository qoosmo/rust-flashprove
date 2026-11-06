# D6 openings audit: the first chain's file-only bytes

Pinned upstream: `9e2bdd8ff5bf9c62f18263d7dac189b0400b260c`. Fixture: `examples/accepted-proof`
(proof 4,145,300 bytes; C++ verdict `YES`).

## Result

The 2,679,688 bytes that the trace-guided replay skipped are exactly **20 Merkle openings** of
run-specific trees. There is no other record type, no stored tree, and no byte left over. Each gap
of `NEXT_OPENINGS.md` is one to three whole openings that are read right after a positions round.

The Rust walk (`crates/flashprove-walk`, binary `proof_walk`; the whole file: `PROOF_WALK.md`) reads the whole first chain
sequentially, `[44, 3,160,036)`, and **verifies every opening against the root that its own chain
received**:

```text
rounds_walked=8037   roots_received=22   openings_verified=20
transcript_bytes=480304   opened_bytes_verified=2679688   unaccounted_bytes_in_span=0
merkle_vertices_recorded=76170
cpp_trace_rounds_compared=8037   cpp_openings_compared=20   (all equal)
```

## Where each byte comes from (C++ consumers)

All 20 are read by `read_opened()` (`blocks/iop/context.h`) → `receive_opening()`
(`blocks/tree/opening.h`) → `read_opening()` + `check_opening()` → `tree_check()`
(`blocks/tree/tree.h`), one call per tree of the group, trees in increasing order.

| Gap | Positions round (name) | Tree | a | b | Part widths: main / mask | W | m | given | Bytes | Offset |
|---:|---|---:|---:|---:|---|---:|---:|---:|---:|---:|
| 1 | 1666 (LOC) | 0 | 18 | 17 | 61,3,1,0 / 3,0,0,3 | 71 | 218 | 2038 | 197,760 | 77,804 |
| 1 | 1666 (LOC) | 2 | 18 | – | 6 / 0 | 6 | 218 | 2038 | 84,400 | 275,564 |
| 1 | 1666 (LOC) | 3 | 18 | – | 129 / 0 | 129 | 218 | 2038 | 298,912 | 359,964 |
| 2 | 3206 (LOC) | 4 | 18 | 17 | 6,3,1,23,0 / 0,0,0,3,3 | 39 | 218 | 2014 | 141,184 | 733,332 |
| 2 | 3206 (LOC) | 5 | 18 | – | 3 / 0 | 3 | 218 | 2014 | 78,400 | 874,516 |
| 2 | 3206 (LOC) | 6 | 18 | – | 61 / 0 | 61 | 218 | 2014 | 179,552 | 952,916 |
| 3 | 4868 (LOC) | 7 | 18 | 17 | 6,1,60,3,1,0 / 0,0,3,0,0,3 | 77 | 218 | 2064 | 209,056 | 1,210,044 |
| 3 | 4868 (LOC) | 8 | 18 | – | 6 / 0 | 6 | 218 | 2064 | 85,232 | 1,419,100 |
| 3 | 4868 (LOC) | 9 | 18 | – | 129 / 0 | 129 | 218 | 2064 | 299,744 | 1,504,332 |
| 4 | 6409 (LOC) | 10 | 18 | 17 | 6,3,1,23,0 / 0,0,0,3,3 | 39 | 218 | 2018 | 141,312 | 1,878,508 |
| 4 | 6409 (LOC) | 11 | 18 | – | 3 / 0 | 3 | 218 | 2018 | 78,528 | 2,019,820 |
| 4 | 6409 (LOC) | 12 | 18 | – | 61 / 0 | 61 | 218 | 2018 | 179,680 | 2,098,348 |
| 5 | 7995 (LOC) | 13 | 18 | 17 | 6,1,34,0 / 0,0,3,3 | 47 | 217 | 2015 | 154,752 | 2,347,708 |
| 5 | 7995 (LOC) | 14 | 18 | – | 3 / 0 | 3 | 217 | 2015 | 78,368 | 2,502,460 |
| 5 | 7995 (LOC) | 15 | 18 | – | 81 / 0 | 81 | 217 | 2015 | 213,776 | 2,580,828 |
| 6 | 8000 (CS) | 16 | 18 | 17 | 6,0 / 0,3 | 9 | 218 | 2014 | 88,864 | 2,794,740 |
| 7 | 8007 (CS) | 17 | 17 | 17 | 48,0 / 24,24 | 96 | 55 | 568 | 62,616 | 2,883,884 |
| 8 | 8013 (CS) | 18 | 16 | 16 | 24,0 / 24,24 | 72 | 44 | 428 | 40,800 | 2,946,732 |
| 9 | 8019 (CS) | 19 | 15 | 15 | 24,0 / 24,24 | 72 | 43 | 375 | 38,488 | 2,987,764 |
| 10 | 8021 (BASE) | 20 | 15 | 15 | 3,3 / 3,3 | 12 | 73 | 573 | 28,264 | 3,131,164 |

a = depth (`log_n`), b = mask-row depth (`log_n_zk`), W = column width in elements of F, m = distinct
positions (218 drawn in every LOC round; repeats removed), given = sibling digests. Salt: 40 bytes.
Every opening has m (8 W + 40) + 32·given bytes (R7.8). Tree 1 (sent in round 1 with tree 0) is not
opened in this chain; a later chain (`FRM\x04`) adopts and opens it.

Correction to `NEXT_OPENINGS.md`: the gaps were labelled by the round that *follows* them (`PSC
epsilon`, `FOLD epsilon`, `BASE lambda`). The rounds that *own* them are the positions rounds just
before: `LOC` (gaps 1–5), `CS` (6–9), `BASE` (10).

## What the Rust walk derives itself

| Item | Native rule | Source |
|---|---|---|
| Read size of each round's message | `message_bytes` of the plan entry | R4.3 |
| Nonce | `nonce_bytes` of the plan, only with work bits; message first, then nonce | R5.x, `Rounds::ask` |
| Round kind hashed into each call | from the round's name (29-name table) | R14.11 |
| Roots and tree numbers | a message with r roots and no answers is r digests; trees numbered by receipt | R7.13, `TreeBook::enter`; fails closed on any other layout |
| Positions | first words of the kind-4 round's draw, `draw_positions` of them, `& (2^a − 1)` | R6.10, `PositionsDraw::positions` |
| List of a shorter tree | short list: draws mod 2^b, sorted, de-duplicated | R7.15 |
| Opening size, leaf hash with fill, vertex hash, walk, given count | from shape and list only | R7.3, R7.4, R7.7–R7.9 |
| Run value and configuration digest | computed | R4.5, R4.9 |
| One value per vertex under a root | per-root record, rollback on rejection | R7.14 |

The C++ trace and openings log are read **only after** the walk, by `--compare-trace` and
`--compare-openings`, which check every round's offsets, pieces, nonce position, name, kind and
state, and every opening's offset, length, tree, root, run, parameters and list.

## What is not native yet (stage D7)

1. **First-query bytes** (parameters and statement): still the C++ serialization, audited against
   the public files as before.
2. **Opening schedule** (`tests/vectors/accepted-proof.proof.schedule`): which trees open after
   which positions round, and their widths. In the reference this follows from the statement's
   oracle notices (`lay_trees`) and the protocol code. Upstream's `docs/format/read_proof.py` derives
   depths and widths from first-query items (R7.12, R12.10, R12.16–R12.18, R13.19, R14.4) but finds
   *which* trees open by trial, which a verifier must not do.

## What the Merkle check binds, and what it does not

Bound (a wrong value rejects, see the negative corpus): tree number, depth, total column width,
salt length, run, configuration digest, every position, every symbol, salt and given digest, the
root, and the round after which the opening is read.

**Not bound**: how the total width splits into parts, and `log_n_zk`. The leaf hash sees only the
flat column, so these change how the columns are *read*, not whether they open. Two schedule
mutations that change only these are accepted by the walk and are recorded as such
(`NOT_BOUND_BY_MERKLE`). They must come from the native plan (D7), and the algebraic checks (D9)
enforce them. Also by design (R7.11): two positions with one short position each show their own
copy of a mask symbol, and nothing here makes them agree.

## Negative corpus (first chain; now part of `scripts/proof_negative.py`)

191 cases. For each of the 20 openings: first and last column symbol, salt, first given digest,
last byte, a symbol equal to p, a symbol equal to 2^64 − 1, a truncation inside the opening, and two
leaves swapped. Then a root in round 1, the LOC nonce before the first opening, and an extra byte
inside the chain. Then six schedule mutations that the walk must reject, and the two not-bound cases.

Result: Rust rejects all 189 cases it must reject (classes: `WrongRoot`, `NonCanonical`,
`Truncated`, `WorkNotSatisfied`, `InvalidShape`, `Schedule`). The **clean** pinned `cp_verify`
answers `NO: proof-refused` to every proof mutation. A pair of rejections does not show that the same
check fired on both sides: the Rust class is recorded per case, and C++ gives only its stage name.

## Rest of the proof (stage D8: now walked natively, see `PROOF_WALK.md`)

From the same openings log, the request proof after the first chain holds a **stored-table opening**
at 3,160,340 (138,312 bytes; a = 23, W = 256, m = 53; `IndexKey::read`, `blocks/iop/foldeq.h`), whose
root must come from the trusted key file, then the openings of chain `FRM\x03` (9) and `FRM\x04` (5).
The last opening ends exactly at the end of the file. Chains `FRM\x02`, `LIN\x01`, `LIN\x02` and
`LNK\x01` belong to `key.bin` and the leaf file, which the key and leaf stages read; they are not
part of the proof file.
