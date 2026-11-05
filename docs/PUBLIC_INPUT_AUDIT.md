# D5: public first-query audit — exact scope

The `flashprove-transcript::first_query` module is a strict, bounded Rust
parser of the upstream H821 first query's **serialized** public parameters
and statement. It checks the version, field/hash modes, round plan sizes,
named items, and strict statement ordering.

On the accepted proof it decodes **8,037 plan entries** (8,037 expanded
rounds) and **eight named public parameter items**. It independently
recomputes H(169,0,1; serialized parameters) and checks three external
bindings against actual upstream files:

- `configuration`: H821 digest of policy.txt, layout.txt and KL.bin
- `stored copy`: the leaf/copy index in the proof header
- `the request file's words`: exactly the supplied example.req bytes

Six negative tests mutate those three files, the request, copy index and
serialized parameter bytes; every altered case is rejected by the audit.

**Limit:** C++ still forms the complete first-query bytes and proof plan.
Rust audits those supplied bytes, but does not yet construct all eight
named parameters and every planned round from scratch. This audit cannot
validate Merkle openings or prove a full proof correct. It is not a
standalone Rust verifier.

CI: https://github.com/qoosmo/rust-flashprove/actions/runs/42062180232
Full first-chain replay: docs/TRANSCRIPT.md.
