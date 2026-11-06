#!/usr/bin/env python3
"""Negative corpus for the native first-chain walk (stage D6).

  first_chain_negative.py WALK CP_VERIFY FIXTURE INPUTS [--json OUT] [--no-cpp]

WALK      target/release/first_chain_walk
CP_VERIFY an UNMODIFIED pinned cp_verify (the real verdict)
FIXTURE   upstream examples/accepted-proof
INPUTS    directory with first-parameters.bin, first-statement.bin, first-chain.schedule

For each of the chain's openings (found by running the walk on the genuine
proof) it makes proof mutations: a column symbol, a salt byte, a given
digest, the opening's last byte, a non-canonical symbol (p and 2^64-1), a
truncation inside the opening. It also mutates a root in a SEND seed message,
a work nonce, and the schedule (widths, depth, tree number, round, a dropped
or an extra entry). Every mutation must make the Rust walk reject; every proof
mutation must make C++ answer something other than YES. Rejections are
classified by the Rust error class.
"""
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

P = 0xFFFFFFFF00000001


def walk(walk_bin, proof, fixture, inputs, schedule):
    c = fixture / "config"
    r = subprocess.run([str(walk_bin), str(proof), str(fixture / "example.req"), str(c / "policy.txt"), str(c / "layout.txt"),
                        str(c / "KL.bin"), str(inputs / "first-parameters.bin"), str(inputs / "first-statement.bin"), str(schedule)],
                       capture_output=True, text=True, timeout=300)
    return r.returncode, r.stdout, r.stderr.strip()


def cpp(cp, fixture, proof):
    c = fixture
    r = subprocess.run([str(cp), str(c / "config"), str(c / "ivk"), str(c / "example.req"), str(c / "example.y"), str(proof),
                        "-id", (c / "ID.txt").read_text().strip(), "-q"], capture_output=True, text=True, timeout=600)
    lines = [l for l in r.stdout.strip().splitlines() if l.strip()]
    return r.returncode, lines[-1] if lines else ""


def classify(err):
    for k in ["NonCanonical", "WrongRoot", "Clash", "UnusedGiven", "Truncated", "WorkNotSatisfied", "Schedule", "NoRoot",
              "InvalidShape", "InvalidList", "RootLayout", "Transcript", "Opening", "first-query audit"]:
        if k in err:
            return k
    return "other"


def main():
    a = sys.argv[1:]
    no_cpp = "--no-cpp" in a
    a = [x for x in a if x != "--no-cpp"]
    out = None
    if "--json" in a:
        i = a.index("--json")
        out = a[i + 1]
        del a[i:i + 2]
    if len(a) != 4:
        raise SystemExit(__doc__)
    walk_bin, cp, fixture, inputs = Path(a[0]), Path(a[1]), Path(a[2]), Path(a[3])
    proof = (fixture / "example.proof").read_bytes()
    schedule_text = (inputs / "first-chain.schedule").read_text()

    code, so, se = walk(walk_bin, fixture / "example.proof", fixture, inputs, inputs / "first-chain.schedule")
    if code != 0 or "NATIVE_FIRST_CHAIN_WALK_OK" not in so:
        raise SystemExit(f"genuine proof did not walk: {se}")
    openings = [dict(kv.split("=") for kv in l.split()[1:]) for l in so.splitlines() if l.startswith("opening ")]
    if not no_cpp:
        cc, last = cpp(cp, fixture, fixture / "example.proof")
        if cc != 0 or last != "YES":
            raise SystemExit(f"C++ did not accept the genuine proof: {cc} {last}")

    cases = []  # (name, proof bytes or None, schedule text or None)
    for o in openings:
        off, n, m, g = int(o["offset"]), int(o["bytes"]), int(o["positions"]), int(o["given"])
        leaf = (n - 32 * g) // m
        w = (leaf - 40) // 8
        t = o["tree"]

        def put(at, data):
            b = bytearray(proof)
            b[at:at + len(data)] = data
            return bytes(b)

        def flip(at):
            b = bytearray(proof)
            b[at] ^= 1
            return bytes(b)
        cases += [
            (f"tree{t}:column-symbol", flip(off), None),
            (f"tree{t}:last-column-symbol", flip(off + (m - 1) * leaf + 8 * (w - 1)), None),
            (f"tree{t}:salt", flip(off + 8 * w), None),
            (f"tree{t}:given-digest", flip(off + m * leaf), None),
            (f"tree{t}:last-byte", flip(off + n - 1), None),
            (f"tree{t}:noncanonical-p", put(off, P.to_bytes(8, "little")), None),
            (f"tree{t}:noncanonical-max", put(off + 8 * (w - 1), (2**64 - 1).to_bytes(8, "little")), None),
            (f"tree{t}:truncated-inside", proof[:off + n // 2], None),
            (f"tree{t}:swap-two-leaves", put(off, proof[off + leaf:off + 2 * leaf] + proof[off:off + leaf]), None),
        ]
    # Transcript-side mutations that bear on openings.
    # Round 1 message (two roots) starts at 44; a later root, tree 2, is a 32-byte SEND seed message.
    cases += [("root-of-tree0", bytes(bytearray(proof[:44]) + bytes([proof[44] ^ 1]) + proof[45:]), None)]
    first_open = int(openings[0]["offset"])
    # The LOC round's nonce is the last 8 bytes before the first opening.
    b = bytearray(proof)
    b[first_open - 8] ^= 1
    cases.append(("LOC-nonce-before-first-opening", bytes(b), None))
    cases.append(("extra-byte-inside-chain", proof[:first_open] + b"\0" + proof[first_open:], None))

    lines = schedule_text.splitlines()
    data = [i for i, l in enumerate(lines) if l.startswith("after_round=")]

    def sched(i, pattern, repl):
        l2 = list(lines)
        new = re.sub(pattern, repl, l2[i], count=1)
        assert new != l2[i], (pattern, l2[i])
        l2[i] = new
        return "\n".join(l2) + "\n"
    first, last = data[0], data[-1]
    cases += [
        ("schedule:main-width+1", None, sched(first, r"main=(\d+)", lambda m: f"main={int(m.group(1)) + 1}")),
        ("schedule:log_n-1", None, sched(last, r" log_n=(\d+)", lambda m: f" log_n={int(m.group(1)) - 1}")),
        ("schedule:wrong-tree", None, sched(data[1], r"tree=(\d+)", lambda m: "tree=1")),
        ("schedule:wrong-round", None, sched(first, r"after_round=(\d+)", lambda m: f"after_round={int(m.group(1)) - 1}")),
        ("schedule:dropped-entry", None, "\n".join(l for i, l in enumerate(lines) if i != data[1]) + "\n"),
        ("schedule:extra-entry", None, schedule_text + lines[first].replace("tree=0", "tree=1") + "\n"),
    ]

    # Fields the Merkle check does NOT bind: the leaf hash sees only the flat
    # column (total width W), depth, tree number, salt, run and position. How W
    # splits into parts, and the mask rows' short length, only change how the
    # columns are read (TreeBook::sort_out), so only the algebraic checks (D9)
    # can catch them. They must come from the native plan (D7). Recorded, not hidden.
    unbound = [
        ("schedule:mask-width-moved", sched(first, r"mask=(\d+),(\d+)", lambda m: f"mask={m.group(2)},{m.group(1)}")),
        ("schedule:log_n_zk-1", sched(first, r"log_n_zk=(\d+)", lambda m: f"log_n_zk={int(m.group(1)) - 1}")),
    ]

    results, failures = [], []
    with tempfile.TemporaryDirectory() as d:
        d = Path(d)
        for name, pb, st in cases:
            pp = fixture / "example.proof"
            sp = inputs / "first-chain.schedule"
            if pb is not None:
                pp = d / "m.proof"
                pp.write_bytes(pb)
            if st is not None:
                sp = d / "m.schedule"
                sp.write_text(st)
            code, so, se = walk(walk_bin, pp, fixture, inputs, sp)
            r = {"case": name, "rust_exit": code, "rust_class": classify(se) if code else "ACCEPTED", "rust_error": se[:300]}
            if code == 0:
                failures.append(f"{name}: Rust walk accepted")
            if pb is not None and not no_cpp:
                cc, last = cpp(cp, fixture, pp)
                r["cpp_exit"], r["cpp_last"] = cc, last
                if last == "YES":
                    failures.append(f"{name}: C++ accepted a mutated proof (the mutation does not reach a checked byte)")
            results.append(r)
            print(f"{name:40s} rust={r['rust_class']:16s} cpp={r.get('cpp_last', '-')}")
        for name, st in unbound:
            sp = d / "u.schedule"
            sp.write_text(st)
            code, so, se = walk(walk_bin, fixture / "example.proof", fixture, inputs, sp)
            r = {"case": name, "rust_exit": code, "rust_class": "NOT_BOUND_BY_MERKLE" if code == 0 else classify(se), "expected": "accepted by the Merkle walk; must be enforced by D7 plan + D9 checks"}
            if code != 0:
                failures.append(f"{name}: expected the Merkle-only walk to be blind to this field; it rejected ({se[:120]}): update the test")
            results.append(r)
            print(f"{name:40s} rust={r['rust_class']:16s} (documented limitation)")
    if out:
        Path(out).write_text(json.dumps({"cases": results, "failures": failures}, indent=1))
    print(f"FIRST_CHAIN_NEGATIVE cases={len(results)} rust_rejected={sum(r['rust_exit'] != 0 for r in results)} not_bound_by_merkle={len(unbound)} failures={len(failures)}")
    if failures:
        print("\n".join(failures))
        sys.exit(1)


if __name__ == "__main__":
    main()
