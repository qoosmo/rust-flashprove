#!/usr/bin/env python3
"""Turn C++ test diagnostics into the two explicit non-native inputs of first_chain_walk.

  extract_first_chain_inputs.py TRACE OPENINGS_LOG OUT_DIR

Writes OUT_DIR/first-parameters.bin and OUT_DIR/first-statement.bin (the first
query's serialized parameters and statement: stage D7 will derive these), and
OUT_DIR/first-chain.schedule: for each opening of the first chain, ONLY the
round after which it is read, the tree number and the column widths (plan data;
stage D7 will derive these from the statement's oracle notices).

Deliberately dropped: offsets, lengths, roots, lists, run and parameters
digests. The Rust walk must find those itself; they are compared afterwards.
"""
import sys
from pathlib import Path

FIRST = "46524d01"


def main():
    if len(sys.argv) != 4:
        raise SystemExit(__doc__)
    trace, log, out = Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3])
    out.mkdir(parents=True, exist_ok=True)
    t = {}
    for line in trace.read_text().splitlines():
        if "=" in line:
            k, v = line.split("=", 1)
            t[k] = v
    (out / "first-parameters.bin").write_bytes(bytes.fromhex(t["first_parameters_serialized"]))
    (out / "first-statement.bin").write_bytes(bytes.fromhex(t["first_statement_serialized"]))
    lines = ["# Opening schedule of the first chain (plan data, stage D7 stand-in).",
             "# Generated from C++ diagnostics; only these fields are kept.",
             "# Bound by the Merkle check (a wrong value rejects): tree, log_n, total width, round.",
             "# NOT bound by it: how the width splits into parts, and log_n_zk (they only change how",
             "# columns are read); D7 must derive them and D9 enforces them."]
    for raw in log.read_text().splitlines():
        f = dict(kv.split("=", 1) for kv in raw.split()[1:])
        if f["chain"] != FIRST:
            continue
        if f["stored"] != "0":
            raise SystemExit("stored-tree opening in the first chain: needs a trusted root (D7)")
        lines.append(f"after_round={f['round']} tree={f['tree']} log_n={f['log_n']} log_n_zk={f['log_n_zk']} main={f['main']} mask={f['mask']}")
    (out / "first-chain.schedule").write_text("\n".join(lines) + "\n")
    print(f"wrote {out}/first-parameters.bin, first-statement.bin, first-chain.schedule ({sum(1 for l in lines if l.startswith("after_round=")) } openings)")


if __name__ == "__main__":
    main()
