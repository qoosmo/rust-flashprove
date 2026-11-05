#!/usr/bin/env python3
"""Test-only C++ instrumentation for first 512 *real* first-chain rounds.

Run AFTER instrument_upstream_first_round.py on the PINNED checkout. Never
build this version as a production verifier. Logs each transcript message's
source byte offsets as observed by the original C++ Reader, plus a domain-
separated message digest and resulting transcript state. File-only Merkle
opening bytes are NOT checked by the Rust replay.
"""
from pathlib import Path
import sys

LIMIT = 512
PREFIX = "RUSTFLASH_BULK_512"
def replace(s, old, replacement, context):
    if s.count(old) != 1:
        raise RuntimeError(f"{context}: expected unique anchor, got {s.count(old)}")
    return s.replace(old, replacement, 1)

def main():
    if len(sys.argv) != 2:
        raise SystemExit("usage: instrument_upstream_round_events.py upstream-src/blocks/chain/rounds.h")
    rounds = Path(sys.argv[1])
    message_h = rounds.parents[1] / "iop" / "message.h"
    s = rounds.read_text()
    m = message_h.read_text()
    if PREFIX in s:
        raise RuntimeError("bulk instrumentation already installed")
    if "RUSTFLASH_FIRST_ROUND_TRACE" not in s:
        raise RuntimeError("first-round C++ instrumentation must be installed before bulk instrumentation")
    m = replace(m,
        "  bool at_end() const { return ok_ && p_ == end_; }\n",
        "  bool at_end() const { return ok_ && p_ == end_; }\n"
        "  size_t rustflash_remaining() const { return (size_t)(end_ - p_); }\n",
        "Reader remaining")
    # The Rounds base class knows the exact message and canonical hash state
    # after the ordinary C++ proof-of-work checks. It has no Reader.
    marker = "    message_.clear();\n    roots_ = answers_ = 0;\n"
    logging = r'''    // RUSTFLASH_BULK_512: test-only replay oracle for the current message.
    if (chain_->label() == 0x46524d01ULL && chain_->rounds() <= 512) {
      if (std::FILE *f = rustflash_trace_open()) {
        const auto rno = (unsigned long long)chain_->rounds();
        std::fprintf(f, "bulk_%llu_name=%s\n", rno, entry.name.c_str());
        std::fprintf(f, "bulk_%llu_kind=%u\n", rno, (unsigned)number_of(entry.kind));
        std::fprintf(f, "bulk_%llu_work=%u\n", rno, (unsigned)entry.work_bits);
        std::fprintf(f, "bulk_%llu_nonce=%llu\n", rno, (unsigned long long)n);
        std::fprintf(f, "bulk_%llu_size=%zu\n", rno, message_.size());
        Hasher hh(Tag(Domain::STATEMENT), 0);
        hh.push(message_.data(), message_.size());
        const Digest hd = hh.finish();
        blk::u8 dig[32];
        digest_to_bytes(hd, dig);
        std::fprintf(f, "bulk_%llu_msg_hash=", rno);
        for (int j = 0; j < 32; ++j) std::fprintf(f, "%02x", (unsigned)dig[j]);
        std::fputc('\n', f);
        const Digest state = chain_->value();
        digest_to_bytes(state, dig);
        std::fprintf(f, "bulk_%llu_rho=", rno);
        for (int j = 0; j < 32; ++j) std::fprintf(f, "%02x", (unsigned)dig[j]);
        std::fputc('\n', f);
        std::fclose(f);
      }
    }
'''
    s=replace(s,marker,logging+marker,"Rounds::ask")
    # Values entering the Fiat-Shamir message are read in the inherited
    # VerifierRounds::take / recv_u64; file_only() reads are NOT included.
    anchor="class VerifierRounds final : public Rounds {\npublic:\n"
    helper=r'''class VerifierRounds final : public Rounds {
  unsigned long long rustflash_piece_round_ = 0;
  unsigned long long rustflash_piece_index_ = 0;
  void rustflash_piece(size_t size) {
    if (!chain_ || chain_->label() != 0x46524d01ULL || chain_->rounds() >= 512) return;
    const auto rno = (unsigned long long)chain_->rounds() + 1;
    if (rno != rustflash_piece_round_) {
      rustflash_piece_round_ = rno;
      rustflash_piece_index_ = 0;
    }
    if (std::FILE *f = rustflash_trace_open()) {
      std::fprintf(f, "bulk_%llu_piece_%llu=%zu,%zu\n",
                   rno, rustflash_piece_index_, r_.rustflash_remaining(), size);
      std::fclose(f);
    }
    ++rustflash_piece_index_;
  }
public:
'''
    s=replace(s,anchor,helper,"VerifierRounds piece counter")
    s=replace(s,
        "    absorb_u64(x);\n    return true;\n",
        "    rustflash_piece(8);\n    absorb_u64(x);\n    return true;\n",
        "recv_u64")
    s=replace(s,
        "    absorb(x);\n    return true;\n",
        "    rustflash_piece(sizeof(T));\n    absorb(x);\n    return true;\n",
        "VerifierRounds::take")
    nonce_marker="    if (!q) return false;\n    n = 0;\n"
    nonce_hook=r'''    if (!q) return false;
    if (chain_->label() == 0x46524d01ULL && chain_->rounds() < 512) {
      if (std::FILE *f = rustflash_trace_open()) {
        std::fprintf(f, "bulk_%llu_nonce_range=%zu,%u\n",
                     (unsigned long long)chain_->rounds() + 1,
                     r_.rustflash_remaining(), (unsigned)plan_->set.nonce_bytes);
        std::fclose(f);
      }
    }
    n = 0;
'''
    s=replace(s,nonce_marker,nonce_hook,"VerifierRounds::nonce")
    rounds.write_text(s)
    message_h.write_text(m)
    print("Test-only first-chain read event offsets and states instrumented for 64 rounds")

if __name__ == "__main__":
    main()
