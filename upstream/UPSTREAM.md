# Upstream reference

- Project: https://github.com/anthropics/FlashProve
- Version: FlashProve 0.16.0 (initial public release)
- Full commit: `9e2bdd8ff5bf9c62f18263d7dac189b0400b260c`
- License: Apache-2.0; copyright Anthropic PBC (2026)
- Primary byte format: `docs/format/FORMAT.md` (particularly R1.x and R13.x–R15.x)
- Header implementation: `blocks/frame/heads.h` and `verifier/src/vf_input_files.h`
- C++ entry: `verifier/src/cp_verify.cpp`
- Lean byte-oriented translation: `lean/OnBytes/Main.lean`
- Soundness-spec verifier: see `lean/THEOREM.md` (different from OnBytes translation)
- Golden sample: `examples/accepted-proof/` (synthetic weights, small model)

**Do not update this pin implicitly.** Any update requires a documented version/format audit.
