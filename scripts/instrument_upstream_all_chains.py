#!/usr/bin/env python3
"""Test-only C++ instrumentation of every verifier chain (all labels, all rounds).

Run on a PINNED upstream worktree AFTER instrument_upstream_openings.py (it uses
Reader::rustflash_left). Never use the resulting binary as a verifier. Appends
to $RUSTFLASH_CHAINS_LOG.<pid> (one file per stage process):

  chain label=<hex> left=<bytes left before the salt> salted=<0|1> salt_in_proof=<0|1>
        salt=<hex> rho0=<hex> parameters_serialized=<hex> statement_serialized=<hex>
  round label=<hex> r=<k> name=<..> kind=<wire> work=<b> nonce=<n> size=<bytes> rho=<hex>
  piece label=<hex> r=<k> left=<n> size=<bytes>       (a value absorbed into round k)
  nonce label=<hex> r=<k> left=<n> size=<bytes>
  seal  label=<hex> digest=<hex>

Names with spaces are written with '_' for ' '. `left` counts bytes left in the
Reader before the read; the file offset is (file length - left).
"""
from pathlib import Path
import sys

TAG = "RUSTFLASH_CHAINS"


def replace(s, old, new, ctx):
    if s.count(old) != 1:
        raise RuntimeError(f"{ctx}: expected one anchor, found {s.count(old)}")
    return s.replace(old, new, 1)


HELPERS = r'''
// RUSTFLASH_CHAINS: test-only log of all chains; changes no decision.
#include <cstdio>
#include <cstdlib>
#include <mutex>
#include <string>
#include <thread>
#include <unistd.h>
namespace blk {
inline std::mutex &rustflash_chains_mu() { static std::mutex m; return m; }
inline std::FILE *rustflash_chains_open() {  // one file per process: <prefix>.<pid>
  const char *p = std::getenv("RUSTFLASH_CHAINS_LOG");
  return p && *p ? std::fopen((std::string(p) + "." + std::to_string((int)getpid())).c_str(), "a") : nullptr;
}
inline void rustflash_chains_hex(std::FILE *f, const u8 *p, size_t n) {
  for (size_t i = 0; i < n; i++) std::fprintf(f, "%02x", (unsigned)p[i]);
}
inline void rustflash_chains_digest(std::FILE *f, const Digest &d) {
  u8 b[32];
  digest_to_bytes(d, b);
  rustflash_chains_hex(f, b, 32);
}
inline std::string rustflash_chains_name(const std::string &s) {
  std::string t = s;
  for (char &c : t) if (c == ' ') c = '_';
  return t;
}
}  // namespace blk
'''


def main():
    if len(sys.argv) != 2:
        raise SystemExit("usage: instrument_upstream_all_chains.py UPSTREAM_ROOT")
    root = Path(sys.argv[1])
    rounds = root / "blocks/chain/rounds.h"
    s = rounds.read_text()
    if TAG in s:
        raise RuntimeError("already instrumented")
    if "rustflash_left" not in (root / "blocks/iop/message.h").read_text():
        raise RuntimeError("run instrument_upstream_openings.py first")
    s = replace(s, "namespace blk {\n", HELPERS + "\nnamespace blk {\n", "helpers")

    # Every round, after the ordinary step.
    s = replace(s, "    message_.clear();\n    roots_ = answers_ = 0;\n",
                r'''    if (chain_) {  // RUSTFLASH_CHAINS
      std::lock_guard<std::mutex> g(rustflash_chains_mu());
      if (std::FILE *f = rustflash_chains_open()) {
        std::fprintf(f, "round label=%llx r=%llu name=%s kind=%u work=%u nonce=%llu size=%zu rho=",
                     (unsigned long long)chain_->label(), (unsigned long long)chain_->rounds(), rustflash_chains_name(entry.name).c_str(),
                     (unsigned)number_of(entry.kind), (unsigned)entry.work_bits, (unsigned long long)n, message_.size());
        rustflash_chains_digest(f, chain_->value());
        std::fputc('\n', f);
        std::fclose(f);
      }
    }
    message_.clear();
    roots_ = answers_ = 0;
''', "Rounds::ask")

    # Seals.
    s = replace(s, "    sealed_ = true;\n    if (!ok()) fate_->refused = true;\n",
                r'''    sealed_ = true;
    {  // RUSTFLASH_CHAINS
      std::lock_guard<std::mutex> g(rustflash_chains_mu());
      if (std::FILE *f = rustflash_chains_open()) {
        std::fprintf(f, "seal label=%llx digest=", (unsigned long long)chain_->label());
        rustflash_chains_digest(f, digest);
        std::fputc('\n', f);
        std::fclose(f);
      }
    }
    if (!ok()) fate_->refused = true;
''', "Rounds::seal")

    # First query of each verifier chain.
    s = replace(s,
                "    FirstQuery q = query_of(b, Digest{});\n    if (q.salted && q.salt_in_proof && !r_.get(q.salt)) {\n",
                "    FirstQuery q = query_of(b, Digest{});\n    const size_t rustflash_left0 = r_.rustflash_left();\n"
                "    if (q.salted && q.salt_in_proof && !r_.get(q.salt)) {\n", "VerifierRounds salt")
    s = replace(s, "      fail(\"the chain's salt is missing\");\n    }\n    start(q);\n    configuration_ = b.configuration_digest();\n    keep_marks(b);\n",
                r'''      fail("the chain's salt is missing");
    }
    start(q);
    configuration_ = b.configuration_digest();
    keep_marks(b);
    {  // RUSTFLASH_CHAINS
      std::lock_guard<std::mutex> g(rustflash_chains_mu());
      if (std::FILE *f = rustflash_chains_open()) {
        std::fprintf(f, "chain label=%llx pid=%d tid=%zu left=%zu salted=%d salt_in_proof=%d salt=", (unsigned long long)q.label, (int)getpid(),
                     std::hash<std::thread::id>{}(std::this_thread::get_id()), rustflash_left0, q.salted ? 1 : 0,
                     q.salt_in_proof ? 1 : 0);
        rustflash_chains_digest(f, q.salt);
        std::fprintf(f, " rho0=");
        rustflash_chains_digest(f, chain_->value());
        std::fprintf(f, " parameters_serialized=");
        rustflash_chains_hex(f, b.parameter_bytes().data(), b.parameter_bytes().size());
        std::fprintf(f, " statement_serialized=");
        rustflash_chains_hex(f, b.statement_bytes().data(), b.statement_bytes().size());
        std::fputc('\n', f);
        std::fclose(f);
      }
    }
''', "VerifierRounds first query")

    piece = r'''  void rustflash_piece(const char *what, size_t size) {  // RUSTFLASH_CHAINS
    if (!chain_) return;
    std::lock_guard<std::mutex> g(rustflash_chains_mu());
    if (std::FILE *f = rustflash_chains_open()) {
      std::fprintf(f, "%s label=%llx r=%llu left=%zu size=%zu\n", what, (unsigned long long)chain_->label(),
                   (unsigned long long)chain_->rounds() + 1, r_.rustflash_left(), size);
      std::fclose(f);
    }
  }
'''
    s = replace(s, "  [[nodiscard]] bool recv_u64(u64 &x) {\n    item(Item::PLAIN);\n    x = 0;\n    if (!ok()) return false;\n",
                piece + "  [[nodiscard]] bool recv_u64(u64 &x) {\n    item(Item::PLAIN);\n    x = 0;\n    if (!ok()) return false;\n"
                "    rustflash_piece(\"piece\", 8);\n", "recv_u64")
    s = replace(s, "  template <class T> bool take(T &x) {\n    x = T{};\n    if (!ok()) return false;\n",
                "  template <class T> bool take(T &x) {\n    x = T{};\n    if (!ok()) return false;\n    rustflash_piece(\"piece\", sizeof(T));\n",
                "take")
    s = replace(s, "  bool nonce(const ChainPrefix &, unsigned, u64 &n) override {\n    const u8 *q = r_.take(plan_->set.nonce_bytes);\n",
                "  bool nonce(const ChainPrefix &, unsigned, u64 &n) override {\n    rustflash_piece(\"nonce\", plan_->set.nonce_bytes);\n"
                "    const u8 *q = r_.take(plan_->set.nonce_bytes);\n", "nonce")
    rounds.write_text(s)
    print("instrumented all chains:", rounds)


if __name__ == "__main__":
    main()
