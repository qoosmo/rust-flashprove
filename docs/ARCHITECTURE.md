# Architecture: protocol semantics and executable trust boundaries

Pinned reference: `9e2bdd8ff5bf9c62f18263d7dac189b0400b260c`.

```text
                      FlashProve protocol + byte format
                       docs/format/FORMAT.md
                                 |
                  +--------------+------------------+
                  |              |                  |
          Lean soundness     C++ cp_verify     RustFlashProve
          verifier          executable         independent
                  |              |                  |
             theorem       result & traces     strict formats
             assumptions         |            field, headers, requests
                  |              |                  |
                  +------- future correspondence ---+
```

**Distinguish Lean targets:**

1. `lean/THEOREM.md`: the protocol verifier with a soundness theorem. It is not C++ cp_verify.
2. `lean/OnBytes/Main.lean`: hand-translation of C++ (not an independent formal correctness
   guarantee). Its `main` is not provided by upstream as a standalone executable.
3. `lean/Ask/` and `lean-verify` references: executable test route; map exact corpus invocation
   before comparing verdicts.

**C++ entry**: `verifier/src/cp_verify.cpp`, built by `verifier/build.sh` into `bin/cp_verify`.
Three stages: key (anchor proof), leaf (link to anchor), request (submitted proof).
The ID is externally authenticated, not read from the proof provider's files.

**Input contract**: `cp_verify CONFIG_DIR PUBLIC_KEY_DIR REQUEST_FILE TOKEN_FILE PROOF_FILE -id ID`.
Config: `policy.txt`, `KL.bin`, `layout.txt`; IVK: `key.bin`, `leaf/<k>.bin`.
Request is T+2 little-endian 32-bit words (T tokens, r, e); token file is a single u32.

**Binary format H821**: `CPPF` + `H821` + little-endian u32 leaf-table index, then a
plan-dependent proof payload; `CPIK` + `H821` for key; `CPEN` + `H821` for leaf.
Proof files have no total-length field. All three kinds require *complete* protocol decoding
to reject unexpected trailing bytes. The current Rust parser checks only their prefixes.

**Arithmetic**: F = Z/(2^64 - 2^32 + 1), E = F[X]/(X^3 - 2); canonical 64-bit LE words,
E as 3 consecutive canonical F words. Both are implemented in simple unoptimized Rust.

**Hash and transcript**: upstream uses BLAKE2b with domain separation and plan-aware
Fiat-Shamir rounds; exact byte order and hash operations are *not yet implemented* in Rust.

**Commitments**: upstream uses tree commitments, openings, proof-of-work, subproof and
sumcheck checks. Rust has no such verification code yet.

## Design rules

- No ``accept`` result for partially decoded proofs.
- Every read is length checked; field elements are canonical or rejected.
- Hash raw file bytes as specified when transcript is added: do not re-serialize policy/layout.
- Separate formatting/structural failures from a cryptographic NO verdict.
- Avoid propagating C++'s unchecked indexing or global state to Rust.
- Keep upstream outputs and exact parameters for every differential test vector.
