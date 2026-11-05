#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
echo '[1/3] Formatting (normalizes the bootstrap source tree)'
cargo fmt --all
cargo fmt --all -- --check
echo '[2/3] Clippy'
cargo clippy --workspace --all-targets -- -D warnings
echo '[3/3] Tests'
cargo test --workspace
echo 'LOCAL RUST CHECKS COMPLETE (not a FlashProve proof-verifier audit)'
