# D8 proof walk: the whole proof file, natively, to the last byte

Pinned upstream: `9e2bdd8ff5bf9c62f18263d7dac189b0400b260c`. Fixture: `examples/accepted-proof`.
Binary: `proof_walk` (`crates/flashprove-walk`). The first chain's openings in detail:
`OPENINGS_AUDIT.md`.

## Result

```text
proof_bytes=4145300  head=[0,12)
chain 46524d01 (first):  [12,3160036)       salt in proof  rounds=8037 roots=22 openings=20  seal=8834e79f…
place:                   [3160036,3160276)  place=28  binding_root=89432683…
chain 46524d03 (shared): [3160276,3842596)  salt = binding root  rounds=42 roots=8 openings=10  seal=2ad2f799…
chain 46524d04 (second): [3842596,4145300)  salt in proof  rounds=16 roots=2 openings=5
bytes: head 12 + salts 64 + transcript 811736 + openings 3333248 + place 240 = 4145300
unaccounted_bytes=0   merkle_vertices_recorded=94436
cpp_chains_compared=3 rounds=8095   cpp_openings_compared=35   (all equal)
```

The layout is `blocks/frame/check.h`'s `head | first chain | place | shared chain | second chain`
(R14.3). The key file's and the leaf file's chains (`FRM\x02`, `LIN\x01`, `LIN\x02`, `LNK\x01`) are
not in the proof file; the key and leaf stages read them (stage D10 will need them, see below).

## What the walk checks natively, beyond D6

| Check | Rule | Reference |
|---|---|---|
| Every chain's first value from its own run value and statement | R4.5, R4.6 | `Rounds::start` |
| First chain's seal: the 4 words drawn by its `SEAL` round | R6.8 | `Rounds::seal` |
| Place: index below $2^{6}$, salt, 6 siblings; leaf $H(173,0,2^6+\text{place}; \text{seal}_1 \,\|\, \text{salt})$, vertices $H(178,\dots)$, both from the configuration digest | R7.18 | `lin_binding_root` |
| Binding tree shape from the first chain's parameter `binding tree` | | `bind_request_parameters` |
| Shared chain: parameters exactly `configuration, codes, the test on the table`; `codes` and the test equal to the first chain's | | `bind_shared_chain`, `lin_bind` |
| Shared chain: statement exactly `table, the binding tree's root`; table byte-equal to the first chain's; root equal to the computed one | | `lin_bind_shared` |
| Shared chain's random bytes are the binding root (not in the file) | R4.5 (b) | `random_bytes_are` |
| Second chain: parameters exactly `configuration`; statement exactly $(\text{seal}_1, \text{seal}_3)$ in this order | | `lin_bind_second`, `Binder::follows` |
| Stored-table opening: root from the `table` item, domain 174, tree number 0, configuration start | R7.4, R8.7 | `IndexKey::read` |
| Adopted trees: a tree of an earlier chain opened under **that** chain's run, only if this chain follows it | R7.4, R7.13 | `TreeBook::adopt`, `lin_adopt` |
| A tree opened at two lists: one value per vertex under its root, across chains | R7.14 | `VerifierSession::record` |
| Roots inside a message: after the answers, in tree order, before a kind-2 round's hiding sum | R8.3, R8.4, R8.6 | |
| No byte after the second chain | R8.1 | `VerifierRounds::finish` |

## Not native yet (stage D7)

1. **First-query bytes** of the three chains (`{first,shared,second}-{parameters,statement}.bin`).
   The walk checks them item by item as above, but the first chain's parameters (plan, codes, the
   test on the table, the request's shape, layout, identifiers, pending rows, binding tree) are
   still the C++ serialization, audited against the public files only through the configuration
   digest and the request items.
2. **Opening schedule** (`tests/vectors/accepted-proof.proof.schedule`): which trees open after
   which positions round, with their root sources and widths.
3. **The table's root itself** is taken from the first query's `table` item. Its authenticity
   comes from the key file and the commitment ID (`-id`), which the key and leaf stages check
   (`check_key`, `check_entry`). Until those stages are ported, a walk of the proof alone cannot
   tell the committed table from another one with a consistent proof: this is a trust input, not a
   proof byte.

## What the Merkle check does not bind (unchanged from D6)

How a column's width splits into parts, and `log_n_zk`, change how columns are read, not whether
they open. Two schedule mutations that change only these are accepted and recorded as
`NOT_BOUND_BY_MERKLE`. Also: the second chain's statement items are compared with seals this walk
computed, but nothing here checks the *algebra* that the seals summarize (stage D9).

## Negative corpus (`scripts/proof_negative.py`)

350 cases: 329 proof mutations, 9 first-query mutations, 10 schedule mutations that must reject,
2 not-bound cases.

- Each of the 35 openings: first and last column symbol, salt, a given digest, last byte, symbol =
  p, symbol = 2^64 − 1, truncation inside, two leaves swapped.
- Place: index, index out of range, salt, a sibling, one sibling too many.
- Each chain: its random bytes (where in the file) and its first message or nonce byte.
- File: a byte appended, the last byte removed, the head's magic, the stored-copy number.
- First queries: shared binding root, shared table root and record, shared codes and
  configuration, the second chain's first seal, the two seals swapped, the second chain's
  configuration, the first chain's table root.
- Schedule: widths, depth, tree number, round, a dropped and an extra entry, the stored tree's
  salt, an adopted tree's root from the wrong chain, a first-chain tree read under the second
  chain's run, a stored tree read as a run tree.

Result: Rust rejects all 348 cases it must reject. The clean pinned `cp_verify` answers something
other than `YES` to every proof mutation. Rejection classes are recorded per case in the JSON
report; equal verdicts do not show that the same check fired on both sides.
