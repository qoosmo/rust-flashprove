#!/usr/bin/env python3
"""Turn C++ test diagnostics into the explicit non-native inputs of proof_walk.

  extract_proof_inputs.py CHAINS_LOG OPENINGS_LOG PROOF OUT_DIR

Writes, for the proof's three chains (first, shared, second):
  OUT_DIR/{first,shared,second}-{parameters,statement}.bin
    each chain's serialized first query (stage D7 will derive these);
  OUT_DIR/proof.schedule
    for every opening the request stage read: the chain, the positions round
    after which it is read, the tree number, the SOURCE of its root (which
    chain received it, at which index, or `table`), and the column widths.

Deliberately dropped: offsets, lengths, root values, lists, run and parameter
digests. proof_walk must find those itself; they are compared afterwards.
"""
import struct
import sys
from pathlib import Path

LABELS = {"46524d01": "first", "46524d03": "shared", "46524d04": "second"}


def fields(line):
    return dict(kv.split("=", 1) for kv in line.split()[1:])


def plan_rounds(params):
    """Expanded (name, roots) per round from a serialized parameter list."""
    at = 0

    def word():
        nonlocal at
        v = struct.unpack_from("<Q", params, at)[0]
        at += 8
        return v

    def sized():
        n = word()
        nonlocal at
        v = params[at:at + n]
        at += n
        return v
    sized(), sized()
    head = [word() for _ in range(8)]
    out = []
    for _ in range(head[7]):
        name = sized().decode()
        w = [word() for _ in range(11)]
        out += [(name, w[3])] * w[0]  # count, work, message_bytes, roots, ...
    return out


def main():
    if len(sys.argv) != 5:
        raise SystemExit(__doc__)
    chains_log, openings_log, proof_path, out = map(Path, sys.argv[1:])
    out.mkdir(parents=True, exist_ok=True)
    proof = proof_path.read_bytes()
    L = len(proof)

    starts, pid = {}, None
    for line in chains_log.read_text().splitlines():
        if line.startswith("chain "):
            f = fields(line)
            if f["label"] in LABELS:
                if f["label"] == "46524d01":
                    pid = f["pid"]
                starts[f["label"]] = L - int(f["left"])
                name = LABELS[f["label"]]
                (out / f"{name}-parameters.bin").write_bytes(bytes.fromhex(f["parameters_serialized"]))
                (out / f"{name}-statement.bin").write_bytes(bytes.fromhex(f["statement_serialized"]))
    if pid is None or len(starts) != 3:
        raise SystemExit("the log does not hold the proof's three chains")

    # Message bytes per (chain, round), from the pieces C++ absorbed; first read offset per round.
    msgs, first_read = {}, {}
    for line in chains_log.read_text().splitlines():
        if line.startswith(("piece ", "nonce ")):
            f = fields(line)
            if f["label"] not in LABELS:
                continue
            k = (f["label"], int(f["r"]))
            s = L - int(f["left"])
            first_read.setdefault(k, s)
            if line.startswith("piece "):
                msgs[k] = msgs.get(k, b"") + proof[s:s + int(f["size"])]
    received = {}
    for lab, name in LABELS.items():
        rounds = plan_rounds((out / f"{name}-parameters.bin").read_bytes())
        roots = []
        for r, (_, nroots) in enumerate(rounds, 1):
            if nroots:
                m = msgs.get((lab, r), b"")
                roots += [m[i:i + 32] for i in range(0, 32 * nroots, 32)]
        received[lab] = roots

    order = sorted(starts, key=starts.get)
    lines = ["# Opening schedule of the proof (plan data, stage D7 stand-in).",
             "# Generated from C++ diagnostics; only these fields are kept.",
             "# Bound by the Merkle check (a wrong value rejects): chain, round, tree, root source,",
             "# log_n, total width, salt. NOT bound by it: how the width splits into parts, and",
             "# log_n_zk (they only change how columns are read); D7 must derive them, D9 enforces them."]
    for raw in openings_log.read_text().splitlines():
        f = fields(raw)
        if f["pid"] != pid:
            continue  # the key and leaf stages read other files
        off = L - int(f["reader_left_before"])
        if f["chain"] in LABELS:
            chain, after = f["chain"], int(f["round"])
        else:  # a stored table, read through IndexKey::read: no chain label in the log
            chain = [c for c in order if starts[c] <= off][-1]
            after = max(r for (c, r), s in first_read.items() if c == chain and s < off)
        root = bytes.fromhex(f["root"])
        if f["stored"] == "1":
            src, salt = "table", f" salt={f['salt']}"
        else:
            hits = [f"{c}:{i}" for c in LABELS for i, x in enumerate(received[c]) if x == root]
            if len(hits) != 1:
                raise SystemExit(f"root of tree {f['tree']} at {off}: {len(hits)} sources")
            src, salt = hits[0], ""
        lines.append(f"chain={chain} after_round={after} tree={f['tree']} root={src} log_n={f['log_n']} "
                     f"log_n_zk={f['log_n_zk']} main={f['main']} mask={f['mask']}{salt}")
    (out / "proof.schedule").write_text("\n".join(lines) + "\n")
    n = sum(1 for l in lines if l.startswith("chain="))
    print(f"wrote {out}: 6 first-query files, proof.schedule ({n} openings)")


if __name__ == "__main__":
    main()
