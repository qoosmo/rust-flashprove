#!/usr/bin/env python3
"""Instrument a PINNED TEMPORARY upstream checkout, not the Rust repository.

Emits diagnostics for the *real* proof's first Fiat-Shamir chain and round.
The changes are limited to file writes and logging of values after the
original operations. Never used for ordinary upstream verification.
"""
from __future__ import annotations
import argparse
from pathlib import Path

MARKER = "RUSTFLASH_FIRST_ROUND_TRACE"
HEADER = '#include <functional>\n'
HELPERS = r'''
// RUSTFLASH_FIRST_ROUND_TRACE: test-only diagnostic hook, no protocol effect.
static inline std::FILE *rustflash_trace_open() {
  const char *path = std::getenv("RUST_FLASH_TRACE_PATH");
  return path && *path ? std::fopen(path, "a") : nullptr;
}
static inline void rustflash_trace_hex(std::FILE *f, const char *key, const blk::u8 *p, size_t n) {
  std::fprintf(f, "%s=", key);
  for (size_t i = 0; i < n; i++) std::fprintf(f, "%02x", (unsigned)p[i]);
  std::fputc('\n', f);
}
static inline void rustflash_trace_digest(std::FILE *f, const char *key, const blk::Digest &d) {
  blk::u8 b[32];
  blk::digest_to_bytes(d, b);
  rustflash_trace_hex(f, key, b, 32);
}
'''
START = "    chain_.reset(new Chain(q));\n"
START_HOOK = r'''    chain_.reset(new Chain(q));
    // RUSTFLASH_FIRST_ROUND_TRACE: first query of a request's real first chain.
    if (q.label == 0x46524d01ULL) {
      if (std::FILE *f = rustflash_trace_open()) {
        std::fprintf(f, "first_label=%llu\n", (unsigned long long)q.label);
        std::fprintf(f, "first_salted=%u\n", (unsigned)q.salted);
        std::fprintf(f, "first_record_len=%zu\n", q.record.size());
        rustflash_trace_digest(f, "first_parameters", q.parameters);
        rustflash_trace_hex(f, "first_statement", q.statement.data(), q.statement.size());
        rustflash_trace_digest(f, "first_salt", q.salt);
        rustflash_trace_digest(f, "first_rho0", chain_->value());
        std::fclose(f);
      }
    }
'''
ASK = "    message_.clear();\n"
ASK_HOOK = r'''    // RUSTFLASH_FIRST_ROUND_TRACE: after the ordinary C++ chain step.
    if (chain_->label() == 0x46524d01ULL && chain_->rounds() == 1) {
      if (std::FILE *f = rustflash_trace_open()) {
        std::fprintf(f, "first_round_name=%s\n", entry.name.c_str());
        std::fprintf(f, "first_round_kind=%u\n", (unsigned)entry.kind);
        std::fprintf(f, "first_round_work=%u\n", (unsigned)entry.work_bits);
        std::fprintf(f, "first_round_nonce=%llu\n", (unsigned long long)n);
        std::fprintf(f, "first_round_nonce_bytes=%u\n", (unsigned)plan_->set.nonce_bytes);
        std::fprintf(f, "first_round_message_bytes=%zu\n", message_.size());
        rustflash_trace_hex(f, "first_round_message", message_.data(), message_.size());
        rustflash_trace_digest(f, "first_rho1", chain_->value());
        std::fclose(f);
      }
    }
    message_.clear();
'''
SAMPLE = "    return nonzero ? chain_->draw_E_nonzero() : chain_->draw_E();\n"
SAMPLE_HOOK = r'''    const E sampled = nonzero ? chain_->draw_E_nonzero() : chain_->draw_E();
    // RUSTFLASH_FIRST_ROUND_TRACE: observe actual draws without drawing again.
    if (chain_->label() == 0x46524d01ULL && chain_->rounds() == 1 && drawn_E_ <= 3) {
      if (std::FILE *f = rustflash_trace_open()) {
        std::fprintf(f, "first_sample_%u=%llu,%llu,%llu\n", drawn_E_,
                     (unsigned long long)sampled.c[0].v,
                     (unsigned long long)sampled.c[1].v,
                     (unsigned long long)sampled.c[2].v);
        std::fprintf(f, "first_sample_%u_nonzero=%u\n", drawn_E_, (unsigned)nonzero);
        std::fclose(f);
      }
    }
    return sampled;
'''

def replacement(s: str, old: str, new: str, tag: str) -> str:
    count = s.count(old)
    if count != 1:
        raise ValueError(f"{tag}: expected 1 unique anchor; got {count}")
    return s.replace(old, new, 1)

def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("rounds_h", type=Path, help="upstream-src/blocks/chain/rounds.h")
    args = parser.parse_args()
    source = args.rounds_h.read_text()
    if MARKER in source:
        raise SystemExit("already instrumented: refusing to patch twice")
    source = replacement(source, HEADER, '#include <cstdio>\n#include <cstdlib>\n'+HEADER, "headers")
    source = replacement(source, "namespace blk {\n", HELPERS+"\nnamespace blk {\n", "namespace")
    source = replacement(source, START, START_HOOK, "start first query")
    source = replacement(source, ASK, ASK_HOOK, "ask first round")
    source = replacement(source, SAMPLE, SAMPLE_HOOK, "draw samples")
    args.rounds_h.write_text(source)
    print("Instrumented pinned upstream's rounds.h (test-only read-only trace hooks)")

if __name__ == "__main__":
    main()
