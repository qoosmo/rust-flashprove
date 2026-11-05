# Stage D5 public-input audit

The parser in `flashprove-transcript::first_query` parses C++-serialized first-query plans, checks H821 encoding, and audits configuration, request and copy bindings. It does not derive the plan independently from model parameters. Local and CI unit tests cover malformed input and mutations.
