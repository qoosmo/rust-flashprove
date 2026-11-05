#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

# Opt-in user-side publication only. This script does not run from ChatGPT.
command -v gh >/dev/null || { echo 'Install GitHub CLI (gh)' >&2; exit 1; }
command -v git >/dev/null || { echo 'git is required' >&2; exit 1; }
command -v cargo >/dev/null || { echo 'Rust cargo is required before publication' >&2; exit 1; }

bash scripts/RUN.sh

if gh repo view qoosmo/rust-flashprove >/dev/null 2>&1; then
  echo 'GitHub repository qoosmo/rust-flashprove exists. Aborting automatic creation; inspect the existing repo.' >&2
  exit 1
fi
if [ ! -d .git ]; then git init -b main; fi
if ! git diff --quiet || ! git diff --cached --quiet || [ -n "$(git ls-files --others --exclude-standard)" ]; then
  git add Cargo.toml crates docs tests upstream scripts README.md LICENSE NOTICE .github .gitignore rust-toolchain.toml
  git commit -m 'feat: bootstrap verifier format and field reference implementation'
fi

gh repo create qoosmo/rust-flashprove --public --source=. --remote=origin --push
printf '\nPublished: https://github.com/qoosmo/rust-flashprove\n'
