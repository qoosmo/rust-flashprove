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

## `accepted-proof.first-chain.schedule`

The opening schedule of the accepted proof's first chain: for each of its 20
Merkle openings, the positions round after which it is read, the tree number
and the column widths. Plan data, generated from test-only C++ diagnostics by
`scripts/extract_first_chain_inputs.py`, and regenerated and diffed in CI. It
holds no offset, length, root, position or digest: the Rust walk finds those
itself. Stage D7 replaces this file with native plan derivation.
