# C++/Rust differential work: actual boundary

Upstream commit: 9e2bdd8ff5bf9c62f18263d7dac189b0400b260c.

Anthropic C++ command (Linux):
bin/cp_verify CONFIG_DIR PUBLIC_KEY_DIR REQUEST_FILE TOKEN_FILE PROOF_FILE -id COMMITMENT_ID -q

Rust current command:
flashprove inspect-bundle POLICY_FILE REQUEST_FILE TOKEN_FILE PROOF_FILE

**These are not equivalent operations.** C++ checks key, leaf, and request proofs;
Rust inspects only the file header, policy version, request and next token.
Rust does not yet verify a single cryptographic proof and cannot output YES.

The workflow differential-smoke.yml clones the pinned upstream commit, builds
its C++ reference verifier on Ubuntu and the Rust inspection CLI, then runs
scripts/differential_smoke.py on six cases.

- Honest proof: C++ must say YES; Rust must report structurally readable, NOT VERIFIED.
- Header truncated/wrong tag/wrong version: both must reject structurally.
- Proof body bitflip/extra trailing byte: C++ must reject, while the Rust header-only
  probe is expected NOT to catch this yet. This is evidence of a known gap,
  not an equivalence result.

The report explicitly states full_rust_verification=false and
semantic_equivalence_established=false.

Next actual milestones: planned round parser with exact EOF consumption,
BLAKE2b transcript and challenge vectors, key/leaf/commitment/opening checks,
full Rust acceptance of upstream honest proof, then genuine verdict
differentials over the mutation corpus. Finite tests do not prove universal
semantic equivalence.
