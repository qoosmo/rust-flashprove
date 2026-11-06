#!/usr/bin/env python3
"""Test-only: turn on upstream's own block-by-block comparison notes in check_proof.

`VerifierContext::notes` (blocks/iop/context.h) records intermediate values,
such as a claim's target after each block, "for comparing a second
implementation of the verifier block by block"; no decision reads them. This
patch points `notes` of the three proof chains' contexts at local vectors and
writes them to $RUSTFLASH_NOTES_LOG.<pid> as

  note chain=<label hex> i=<k> what=<name, spaces as '_'> value=<c0>,<c1>,<c2>

Run on a PINNED upstream worktree. Never use the result as a verifier.
"""
from pathlib import Path
import sys

TAG = "RUSTFLASH_NOTES"


def replace(s, old, new, ctx):
    if s.count(old) != 1:
        raise RuntimeError(f"{ctx}: expected one anchor, found {s.count(old)}")
    return s.replace(old, new, 1)


HELPER = r'''
// RUSTFLASH_NOTES: test-only dump of VerifierContext::notes; changes no decision.
#include <cstdio>
#include <cstdlib>
#include <string>
#include <unistd.h>
namespace blk {
inline void rustflash_dump_notes(u64 label, const std::vector<std::pair<std::string, E>> &notes) {
  const char *p = std::getenv("RUSTFLASH_NOTES_LOG");
  if (!p || !*p) return;
  std::FILE *f = std::fopen((std::string(p) + "." + std::to_string((int)getpid())).c_str(), "a");
  if (!f) return;
  for (size_t i = 0; i < notes.size(); i++) {
    std::string w = notes[i].first;
    for (char &c : w) if (c == ' ') c = '_';
    const E &v = notes[i].second;
    std::fprintf(f, "note chain=%llx i=%zu what=%s value=%llu,%llu,%llu\n", (unsigned long long)label, i, w.c_str(),
                 (unsigned long long)v.c[0].v, (unsigned long long)v.c[1].v, (unsigned long long)v.c[2].v);
  }
  std::fclose(f);
}
}  // namespace blk
'''


def main():
    if len(sys.argv) != 2:
        raise SystemExit("usage: instrument_upstream_notes.py UPSTREAM_ROOT")
    check = Path(sys.argv[1]) / "blocks/frame/check.h"
    s = check.read_text()
    if TAG in s:
        raise RuntimeError("already instrumented")
    s = replace(s, "namespace blk {\n", HELPER + "\nnamespace blk {\n", "helper")
    s = replace(s, "  VerifierContext first_V(x.lin.codes, first_ch);\n",
                "  VerifierContext first_V(x.lin.codes, first_ch);\n"
                "  std::vector<std::pair<std::string, E>> rustflash_first_notes;  // RUSTFLASH_NOTES\n"
                "  first_V.notes = &rustflash_first_notes;\n", "first context")
    s = replace(s, "  if (!first_ch.seal(R_SEAL, seal) || !first_ch.finish_inside_a_file()) return no(first_ch, \"first chain: its end\");\n",
                "  rustflash_dump_notes(LABEL_FIRST_CHAIN, rustflash_first_notes);\n"
                "  rustflash_first_notes.clear();\n"
                "  if (!first_ch.seal(R_SEAL, seal) || !first_ch.finish_inside_a_file()) return no(first_ch, \"first chain: its end\");\n",
                "first chain end")
    s = replace(s, "  VerifierContext shared_V(shared_x.codes, shared_ch);\n",
                "  VerifierContext shared_V(shared_x.codes, shared_ch);\n"
                "  std::vector<std::pair<std::string, E>> rustflash_shared_notes;  // RUSTFLASH_NOTES\n"
                "  shared_V.notes = &rustflash_shared_notes;\n", "shared context")
    s = replace(s, "  shared_V.st.require_all_tested();\n",
                "  shared_V.st.require_all_tested();\n"
                "  rustflash_dump_notes(LABEL_PROOF_SHARED_CHAIN, rustflash_shared_notes);\n", "shared end")
    s = replace(s, "  VerifierContext V = lin_go_on(std::move(first_V), second_ch);\n",
                "  VerifierContext V = lin_go_on(std::move(first_V), second_ch);\n"
                "  V.notes = &rustflash_first_notes;  // RUSTFLASH_NOTES: the moved context keeps the pointer\n", "second context")
    s = replace(s, "  V.st.require_all_tested();\n  stands(\"behind the chains\");\n",
                "  V.st.require_all_tested();\n"
                "  rustflash_dump_notes(LABEL_PROOF_SECOND_CHAIN, rustflash_first_notes);\n"
                "  stands(\"behind the chains\");\n", "second end")
    check.write_text(s)
    print("instrumented notes:", check)


if __name__ == "__main__":
    main()
