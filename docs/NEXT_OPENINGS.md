# Stage D6 handoff — make file-only proof records independently checkable

Reference: Anthropic FlashProve commit
`9e2bdd8ff5bf9c62f18263d7dac189b0400b260c`.

## Verified D5 boundary

- H821 first chain: 8,037 physical rounds from the accepted proof.
- Rust independently reassembled C++-observed transcript slices from the
  original proof, checked all message hashes and work nonces, and reproduced
  all 8,037 first-chain Fiat–Shamir states.
- **2,679,688 bytes are unverified file-only gaps** in exactly 10 regions.
  The first is at proof offset 77,804 (581,072 bytes), before round 1,669.
- Full fixture size is 4,145,300 bytes; the final observed read of the first
  chain ends at offset 3,160,036.
- These are test diagnostics, **not full Rust proof verification**.

Evidence:
https://github.com/qoosmo/rust-flashprove/actions/runs/42064654513

## Unverified first-chain regions

| # | Offset | Bytes | Next round |
|---|---:|---:|---:|
| 1 | 77,804 | 581,072 | 1,669 |
| 2 | 733,332 | 399,136 | 3,209 |
| 3 | 1,210,044 | 594,032 | 4,871 |
| 4 | 1,878,508 | 399,520 | 6,412 |
| 5 | 2,347,708 | 446,896 | 7,997 |
| 6 | 2,794,740 | 88,864 | 8,001 |
| 7 | 2,883,884 | 62,616 | 8,008 |
| 8 | 2,946,732 | 40,800 | 8,014 |
| 9 | 2,987,764 | 38,488 | 8,020 |
| 10 | 3,131,164 | 28,264 | 8,023 |

These are **gaps in field reads**, not yet typed into proof record
categories. Do not assert that every byte is a Merkle opening merely because
the upstream protocol uses file-only openings.

## Code and exact constraints to port

- `blocks/tree/opening.h`: `read_opening()`, `check_opening()`,
  `receive_opening()`; each listed leaf has column field elements and salt,
  then the sibling digests required by `tree_walk()`.
- `blocks/tree/tree.h`: sibling traversal, duplicate-position rules,
  root recomputation. Do not guess the number or order of siblings.
- `blocks/chain/rounds.h`: `VerifierRounds::file_only()` separates
  opening records from the Fiat–Shamir prover message.
- `blocks/frame/check.h`: three proof chains, binding tree slot, roots.
- `docs/format/FORMAT.md`, `docs/format/10-proof-file.md`:
  H821 tree labels, shapes, opening ordering and R14.7 proof slot.

## Acceptance criteria for D6

1. Classify gap 1 by the actual opening consumer and reproduce its exact
   read boundaries in independent Rust code, without C++ read-offset input.
2. Parse all symbols canonically, salts and sibling digests with the exact
   position-list order and tree shape; recompute the expected Merkle root.
3. Reject truncation, noncanonical symbols and mutations of each gap's
   data, with comparable C++ and Rust error outcomes.
4. Extend to all 10 first-chain file-only regions. Require that Rust's
   independent cursor consumes exactly the C++-observed first-chain bytes;
   *then* remove C++ offsets for the replay.
5. Only afterward begin shared and second chain parser/checks. The
   algebraic proof equations, full verdict and Lean certification remain open.

Do not use the diagnostic replay to accept a proof. The public Rust
`verify` command must remain fail-closed until every critical check exists.
