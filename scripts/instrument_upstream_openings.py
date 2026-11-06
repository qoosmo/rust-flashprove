#!/usr/bin/env python3
"""Test-only C++ instrumentation: log every Merkle opening the pinned verifier reads.

Run on a PINNED upstream checkout (a separate worktree). Never use the
resulting binary as a verifier. For each `read_opening` call it appends one
line to $RUSTFLASH_OPENINGS_LOG:

  opening reader_left_before=<n> reader_left_after=<n> ok=<0|1> checked=<0|1|->
          chain=<label hex> round=<k> stored=<0|1> tree=<t> log_n=<a> log_n_zk=<b>
          main=<w,w,...> mask=<w,...> salt=<s> run=<hex> params=<hex>
          root=<hex> list=<x,x,...>

`reader_left_*` is the number of bytes left in the Reader the opening was read
from; for the proof's Reader, the file offset is (proof length - left).

The Rust side uses this log ONLY as differential evidence and, until D6.3/D7
land, as the explicitly labelled test source of (shape, list, root). It never
uses the logged offsets to decide what to read.
"""
from pathlib import Path
import sys

TAG = "RUSTFLASH_OPENINGS"


def replace(s, old, new, ctx):
    if s.count(old) != 1:
        raise RuntimeError(f"{ctx}: expected one anchor, found {s.count(old)}")
    return s.replace(old, new, 1)


def main():
    if len(sys.argv) != 2:
        raise SystemExit("usage: instrument_upstream_openings.py UPSTREAM_ROOT")
    root = Path(sys.argv[1])
    msg = root / "blocks/iop/message.h"
    opening = root / "blocks/tree/opening.h"
    rounds = root / "blocks/chain/rounds.h"

    m = msg.read_text()
    if TAG in m:
        raise RuntimeError("already instrumented")
    m = replace(m, "  bool at_end() const { return ok_ && p_ == end_; }\n",
                "  bool at_end() const { return ok_ && p_ == end_; }\n"
                f"  size_t rustflash_left() const {{ return (size_t)(end_ - p_); }} // {TAG}\n",
                "Reader")
    msg.write_text(m)

    r = rounds.read_text()
    r = replace(r, "  u64 word() { return ok() ? chain_->next_word() : 0; }\n",
                "  u64 word() { return ok() ? chain_->next_word() : 0; }\n"
                f"public:\n  u64 rustflash_label() const {{ return chain_ ? chain_->label() : 0; }} // {TAG}\n"
                "  u64 rustflash_rounds() const { return chain_ ? chain_->rounds() : 0; }\nprotected:\n",
                "Rounds accessors")
    rounds.write_text(r)

    o = opening.read_text()
    helper = r'''
// RUSTFLASH_OPENINGS: test-only log; changes no decision.
#include <cstdio>
#include <cstdlib>
#include <mutex>
inline void rustflash_hex(std::FILE *f, const Digest &d) {
  u8 b[DIGEST_BYTES];
  digest_to_bytes(d, b);
  for (size_t i = 0; i < DIGEST_BYTES; i++) std::fprintf(f, "%02x", (unsigned)b[i]);
}
inline void rustflash_log_opening(size_t before, size_t after, bool ok, int checked, u64 label, u64 round, const OracleTreeShape &s,
                                  const Digest &root, const PositionList &list) {
  static std::mutex mu;
  const char *path = std::getenv("RUSTFLASH_OPENINGS_LOG");
  if (!path) return;
  std::lock_guard<std::mutex> g(mu);
  std::FILE *f = std::fopen(path, "a");
  if (!f) return;
  std::fprintf(f, "opening reader_left_before=%zu reader_left_after=%zu ok=%d checked=%d chain=%llx round=%llu stored=%d tree=%u log_n=%u log_n_zk=%u main=",
               before, after, ok ? 1 : 0, checked, (unsigned long long)label, (unsigned long long)round, s.stored ? 1 : 0, (unsigned)s.tree_number, s.log_n, s.log_n_zk);
  for (size_t i = 0; i < s.main_symbols.size(); i++) std::fprintf(f, "%s%zu", i ? "," : "", s.main_symbols[i]);
  std::fprintf(f, " mask=");
  for (size_t i = 0; i < s.mask_symbols.size(); i++) std::fprintf(f, "%s%zu", i ? "," : "", s.mask_symbols[i]);
  std::fprintf(f, " salt=%zu run=", s.salt_bytes);
  rustflash_hex(f, s.run);
  std::fprintf(f, " params=");
  rustflash_hex(f, s.parameters);
  std::fprintf(f, " root=");
  rustflash_hex(f, root);
  std::fprintf(f, " list=");
  for (size_t i = 0; i < list.size(); i++) std::fprintf(f, "%s%llu", i ? "," : "", (unsigned long long)list[i]);
  std::fputc('\n', f);
  std::fclose(f);
}
'''
    o = replace(o, "\n// Hashes a leaf: gives leaf()", helper + "\n// Hashes a leaf: gives leaf()", "helper")
    # receive_opening: run-specific trees inside a chain.
    o = replace(o,
                "  if (!read_opening(ch.file_only(), s, list, o)) {\n"
                "    ch.refuse_what_was_read(\"an opening is cut short or holds a symbol that is not in canonical form\");\n"
                "    return false;\n  }\n"
                "  bool clash = false;\n"
                "  if (!check_opening(root, s, list, o, &seen, &clash)) { // the record is then as it was before\n",
                "  const size_t rf_before = ch.file_only().rustflash_left();\n"
                "  if (!read_opening(ch.file_only(), s, list, o)) {\n"
                "    rustflash_log_opening(rf_before, ch.file_only().rustflash_left(), false, -1, ch.rustflash_label(), ch.rustflash_rounds(), s, root, list);\n"
                "    ch.refuse_what_was_read(\"an opening is cut short or holds a symbol that is not in canonical form\");\n"
                "    return false;\n  }\n"
                "  bool clash = false;\n"
                "  const bool rf_checked = check_opening(root, s, list, o, &seen, &clash);\n"
                "  rustflash_log_opening(rf_before, ch.file_only().rustflash_left(), true, rf_checked ? 1 : 0, ch.rustflash_label(), ch.rustflash_rounds(), s, root, list);\n"
                "  if (!rf_checked) { // the record is then as it was before\n",
                "receive_opening")
    opening.write_text(o)

    # Stored-table reads (foldeq.h IndexKey::read) go through read_opening/check_opening directly.
    fe = root / "blocks/iop/foldeq.h"
    f = fe.read_text()
    f = replace(f,
                "    if (!read_opening(file, tree, at, o) || !check_opening(root, tree, at, o, &session.record(root))) return false;\n",
                "    const size_t rf_before = file.rustflash_left();\n"
                "    const bool rf_read = read_opening(file, tree, at, o);\n"
                "    const bool rf_checked = rf_read && check_opening(root, tree, at, o, &session.record(root));\n"
                "    rustflash_log_opening(rf_before, file.rustflash_left(), rf_read, rf_read ? (rf_checked ? 1 : 0) : -1, 0, 0, tree, root, at);\n"
                "    if (!rf_checked) return false;\n",
                "IndexKey::read")
    fe.write_text(f)
    print("instrumented:", msg, rounds, opening, fe)


if __name__ == "__main__":
    main()
