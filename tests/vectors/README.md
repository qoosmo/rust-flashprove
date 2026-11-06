# Original FlashProve request fixtures

Two files copied byte-for-byte from `anthropics/FlashProve` at commit
`9e2bdd8ff5bf9c62f18263d7dac189b0400b260c`:

- `examples/accepted-proof/example.req` -> `upstream-example.req`
- `examples/accepted-proof/example.y` -> `upstream-example.y`

Copyright 2026 Anthropic PBC, Apache License 2.0.

Validate against upstream `examples/accepted-proof/SHA256SUMS`:

```
ce700974a03d43586d66ca742f9bbc8ad45c936d03dfdb8614dd559a2780aa13  upstream-example.req
add7f2a4843f8c512c0e2875546581db11b9ba227ee008b5f719dfacb125de76  upstream-example.y
```

Sample: 64 token words, then r=60, e=64; y=199.

There is NO included full proof, no claimed acceptance vector, and no independent
validation against cp_verify yet.

## `accepted-proof.proof.schedule`

The opening schedule of the accepted proof: for each of its 35 Merkle openings
(20 in the first chain, 10 in the shared chain including the stored table, 5
in the second chain), the chain and positions round after which it is read,
the tree number, the source of its root (`CHAIN:INDEX` of the roots that chain
received, or `table`), the column widths and, for a stored tree, its salt
length. Plan data, generated from test-only C++ diagnostics by
`scripts/extract_proof_inputs.py`, and regenerated and diffed in CI. It holds
no offset, length, root value, position or digest: `proof_walk` finds those
itself. Stage D7 replaces this file with native plan derivation.

## `shared-chain.codes.hex`, `shared-chain.lin-shape.hex`

The shared chain's bound parameter items `codes` and `the test on the table`
(the `LinShape`), copied from its serialized first query. `flashprove-iop`
parses them and checks that re-serializing gives back exactly these bytes.

## `gl64-points.txt`

`log_n position point` for 48 positions, printed by upstream's `gl64_point`
(`scripts/points_cpp_oracle.cpp`); regenerated and diffed in CI.

## `accepted-proof.notes.txt`

Upstream's own block-by-block comparison notes (`VerifierContext::notes`) for
the accepted proof's three chains (68 + 45 + 21), produced by
`scripts/instrument_upstream_notes.py`; regenerated and diffed in CI. Each port
step of `docs/SHARED_CHAIN_MAP.md` must reproduce its notes exactly.
