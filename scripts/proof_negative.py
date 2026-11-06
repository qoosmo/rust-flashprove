#!/usr/bin/env python3
"""Negative corpus for the native whole-proof walk (stages D6 and D8).

  proof_negative.py WALK CP_VERIFY FIXTURE INPUTS SCHEDULE [--json OUT] [--no-cpp]

WALK      target/release/proof_walk
CP_VERIFY an UNMODIFIED pinned cp_verify (the real verdict)
FIXTURE   upstream examples/accepted-proof
INPUTS    directory with the six first-query files
SCHEDULE  the opening schedule

For each opening (found by walking the genuine proof): the first and last
column symbol, a salt byte, a given digest, the last byte, a non-canonical
symbol (p, 2^64 - 1), a truncation inside it, two leaves swapped. For the
place: its index, salt, a sibling, and one sibling too many. For every chain:
its random bytes (where in the file), its first round's message, its first
work nonce. For the file: a byte appended, the last byte removed. For the
first queries: the shared chain's binding root and table, the second chain's
seals and their order, the configuration item. For the schedule: widths,
depth, tree, round, root source (another chain, table), a dropped and an extra
entry. Every case must make the Rust walk reject; every proof mutation must
make the clean C++ verifier say something other than YES. Two schedule
fields are NOT bound by Merkle checks; they are recorded as such.
"""
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

P = 0xFFFFFFFF00000001
QUERY_FILES = [f"{c}-{k}.bin" for c in ("first", "shared", "second") for k in ("parameters", "statement")]


def walk(walk_bin, proof, fixture, inputs, schedule):
    c = fixture / "config"
    r = subprocess.run([str(walk_bin), str(proof), str(fixture / "example.req"), str(c / "policy.txt"), str(c / "layout.txt"),
                        str(c / "KL.bin"), str(inputs), str(schedule)], capture_output=True, text=True, timeout=300)
    return r.returncode, r.stdout, r.stderr.strip()


def cpp(cp, fixture, proof):
    c = fixture
    r = subprocess.run([str(cp), str(c / "config"), str(c / "ivk"), str(c / "example.req"), str(c / "example.y"), str(proof),
                        "-id", (c / "ID.txt").read_text().strip(), "-q"], capture_output=True, text=True, timeout=600)
    lines = [l for l in r.stdout.strip().splitlines() if l.strip()]
    return r.returncode, lines[-1] if lines else ""


def classify(err):
    for k in ["NonCanonical", "WrongRoot", "Clash", "UnusedGiven", "Truncated", "WorkNotSatisfied", "LeftOver", "Linkage",
              "Place", "Schedule", "NoRoot", "InvalidShape", "InvalidList", "RootLayout", "FirstQuery", "first chain", "Transcript", "Opening"]:
        if k in err:
            return k
    return "other"


def items(b, at=0):
    out = []
    while at < len(b):
        n = int.from_bytes(b[at:at + 8], "little")
        name = b[at + 8:at + 8 + n]
        at += 8 + n
        m = int.from_bytes(b[at:at + 8], "little")
        out.append((name, at + 8, m))  # value offset and length
        at += 8 + m
    return out


def param_items(b):
    """Items of a serialized parameter list, after the version item and the plan."""
    at = 0

    def word():
        nonlocal at
        v = int.from_bytes(b[at:at + 8], "little")
        at += 8
        return v

    def sized():
        nonlocal at
        n = word()
        at += n
    sized(), sized()
    head = [word() for _ in range(8)]
    for _ in range(head[7]):
        sized()
        for _ in range(11):
            word()
    return items(b, at)


def main():
    a = sys.argv[1:]
    no_cpp = "--no-cpp" in a
    a = [x for x in a if x != "--no-cpp"]
    out = None
    if "--json" in a:
        i = a.index("--json")
        out = a[i + 1]
        del a[i:i + 2]
    if len(a) != 5:
        raise SystemExit(__doc__)
    walk_bin, cp, fixture, inputs, schedule = map(Path, a)
    proof = (fixture / "example.proof").read_bytes()
    schedule_text = schedule.read_text()

    code, so, se = walk(walk_bin, fixture / "example.proof", fixture, inputs, schedule)
    if code != 0 or "NATIVE_PROOF_WALK_OK" not in so:
        raise SystemExit(f"genuine proof did not walk: {se}")
    if not no_cpp:
        cc, last = cpp(cp, fixture, fixture / "example.proof")
        if cc != 0 or last != "YES":
            raise SystemExit(f"C++ did not accept the genuine proof: {cc} {last}")
    # Openings and spans, from the walk's own report on the genuine proof.
    spans = {}
    for l in so.splitlines():
        m = re.match(r"chain (\w+): span=\[(\d+),(\d+)\) salt_in_proof=(\w+)", l)
        if m:
            spans[m.group(1)] = (int(m.group(2)), int(m.group(3)), m.group(4) == "true")
        m = re.match(r"place: span=\[(\d+),(\d+)\)", l)
        if m:
            place = (int(m.group(1)), int(m.group(2)))
    openings = parse_openings(walk_bin, fixture, inputs, schedule)

    def put(at, data):
        b = bytearray(proof)
        b[at:at + len(data)] = data
        return bytes(b)

    def flip(at):
        b = bytearray(proof)
        b[at] ^= 1
        return bytes(b)

    cases = []  # (name, proof or None, schedule text or None, inputs override {file: bytes} or None)
    for o in openings:
        off, n, m, g, t, c = o["offset"], o["bytes"], o["positions"], o["given"], o["tree"], o["chain"]
        leaf = (n - 32 * g) // m
        salt = o["salt"]
        w = (leaf - salt) // 8
        tag = f"{c}:tree{t}@{off}"
        cases += [
            (f"{tag}:column-symbol", flip(off), None, None),
            (f"{tag}:last-column-symbol", flip(off + (m - 1) * leaf + 8 * (w - 1)), None, None),
            (f"{tag}:salt", flip(off + 8 * w), None, None),
            (f"{tag}:last-byte", flip(off + n - 1), None, None),
            (f"{tag}:noncanonical-p", put(off, P.to_bytes(8, "little")), None, None),
            (f"{tag}:truncated-inside", proof[:off + n // 2], None, None),
        ]
        if g:
            cases.append((f"{tag}:given-digest", flip(off + m * leaf), None, None))
        if m > 1:
            cases.append((f"{tag}:swap-two-leaves", put(off, proof[off + leaf:off + 2 * leaf] + proof[off:off + leaf]), None, None))
        if w > 1:
            cases.append((f"{tag}:noncanonical-max", put(off + 8 * (w - 1), (2**64 - 1).to_bytes(8, "little")), None, None))
    p0, p1 = place
    cases += [
        ("place:index", flip(p0), None, None),
        ("place:index-out-of-range", put(p0, (1 << 40).to_bytes(8, "little")), None, None),
        ("place:salt", flip(p0 + 8), None, None),
        ("place:sibling", flip(p1 - 1), None, None),
        ("place:one-sibling-more", proof[:p1] + proof[p1 - 32:p1] + proof[p1:], None, None),
    ]
    for c, (s, e, salted) in spans.items():
        if salted:
            cases.append((f"{c}:random-bytes", flip(s), None, None))
        body = s + (32 if salted else 0)
        cases.append((f"{c}:first-message-or-nonce-byte", flip(body), None, None))
    cases += [
        ("file:byte-appended", proof + b"\0", None, None),
        ("file:last-byte-removed", proof[:-1], None, None),
        ("file:head-magic", flip(0), None, None),
        ("file:stored-copy-number", flip(8), None, None),
    ]
    # First-query mutations (inputs only; the proof is genuine).
    q = {f: (inputs / f).read_bytes() for f in QUERY_FILES}

    def qmut(fname, item_name, how):
        b = bytearray(q[fname])
        parse = param_items if fname.endswith("parameters.bin") else items
        hits = [(o, l) for n, o, l in parse(bytes(b)) if n == item_name]
        k = how[0] if isinstance(how, tuple) else 0
        o, l = hits[k]
        # "last": the value's last byte; ("root", k): the 32-byte commitment after the length word.
        delta = l - 1 if how == "last" else (8 if isinstance(how, tuple) and len(how) > 1 and how[1] == "root" else 0)
        b[o + delta] ^= 1
        return {fname: bytes(b)}
    st2 = q["second-statement.bin"]
    it2 = items(st2)
    swapped = bytearray(st2)
    (_, o1, l1), (_, o2, l2) = it2[0], it2[1]
    swapped[o1:o1 + l1], swapped[o2:o2 + l2] = st2[o2:o2 + l2], st2[o1:o1 + l1]
    cases += [
        ("query:shared-binding-root", None, None, qmut("shared-statement.bin", b"the binding tree's root", "first")),
        ("query:shared-table-root", None, None, qmut("shared-statement.bin", b"table", (0, "root"))),
        ("query:shared-table-record", None, None, qmut("shared-statement.bin", b"table", "last")),
        ("query:shared-codes", None, None, qmut("shared-parameters.bin", b"codes", "last")),
        ("query:shared-configuration", None, None, qmut("shared-parameters.bin", b"configuration", "first")),
        ("query:second-seal-1", None, None, qmut("second-statement.bin", b"the seal of an earlier chain", (0,))),
        ("query:second-seals-swapped", None, None, {"second-statement.bin": bytes(swapped)}),
        ("query:second-configuration", None, None, qmut("second-parameters.bin", b"configuration", "first")),
        ("query:first-table-root", None, None, qmut("first-statement.bin", b"table", (0, "root"))),
    ]

    lines = schedule_text.splitlines()
    data = [i for i, l in enumerate(lines) if l.startswith("chain=")]

    def sched(i, pattern, repl):
        l2 = list(lines)
        new = re.sub(pattern, repl, l2[i], count=1)
        assert new != l2[i], (pattern, l2[i])
        l2[i] = new
        return "\n".join(l2) + "\n"
    idx = {k: next(i for i in data if re.search(k, lines[i])) for k in [r"root=table", r"chain=46524d04.*root=46524d03:", r"chain=46524d04.*root=46524d01:"]}
    first = data[0]
    cases += [
        ("schedule:main-width+1", None, sched(first, r"main=(\d+)", lambda m: f"main={int(m.group(1)) + 1}"), None),
        ("schedule:log_n-1", None, sched(data[-1], r" log_n=(\d+)", lambda m: f" log_n={int(m.group(1)) - 1}"), None),
        ("schedule:wrong-tree-number", None, sched(data[1], r"tree=(\d+)", lambda m: "tree=1"), None),
        ("schedule:wrong-round", None, sched(first, r"after_round=(\d+)", lambda m: f"after_round={int(m.group(1)) - 1}"), None),
        ("schedule:dropped-entry", None, "\n".join(l for i, l in enumerate(lines) if i != data[1]) + "\n", None),
        ("schedule:extra-entry", None, schedule_text + re.sub(r"tree=0 root=46524d01:0", "tree=1 root=46524d01:1", lines[first]) + "\n", None),
        ("schedule:stored-salt", None, sched(idx[r"root=table"], r"salt=(\d+)", lambda m: "salt=48"), None),
        ("schedule:adopted-root-from-wrong-chain", None, sched(idx[r"chain=46524d04.*root=46524d03:"], r"root=46524d03:\d+", lambda m: "root=46524d01:5"), None),
        ("schedule:first-chain-tree-under-own-run", None, sched(idx[r"chain=46524d04.*root=46524d01:"], r"root=46524d01:(\d+)", lambda m: "root=46524d04:" + m.group(1)), None),
        ("schedule:stored-as-run-tree", None, sched(idx[r"root=table"], r"root=table(.*) salt=\d+", lambda m: "root=46524d03:0" + m.group(1)), None),
    ]
    unbound = [
        ("schedule:mask-width-moved", sched(first, r"mask=(\d+),(\d+)", lambda m: f"mask={m.group(2)},{m.group(1)}")),
        ("schedule:log_n_zk-1", sched(first, r"log_n_zk=(\d+)", lambda m: f"log_n_zk={int(m.group(1)) - 1}")),
    ]

    results, failures = [], []
    with tempfile.TemporaryDirectory() as d:
        d = Path(d)
        for name, pb, st, qo in cases:
            pp, sp, ip = fixture / "example.proof", schedule, inputs
            if pb is not None:
                pp = d / "m.proof"
                pp.write_bytes(pb)
            if st is not None:
                sp = d / "m.schedule"
                sp.write_text(st)
            if qo is not None:
                ip = d / "q"
                ip.mkdir(exist_ok=True)
                for f in QUERY_FILES:
                    (ip / f).write_bytes(qo.get(f, q[f]))
            code, so, se = walk(walk_bin, pp, fixture, ip, sp)
            r = {"case": name, "rust_exit": code, "rust_class": classify(se) if code else "ACCEPTED", "rust_error": se[:300]}
            if code == 0:
                failures.append(f"{name}: Rust walk accepted")
            if pb is not None and not no_cpp:
                cc, last = cpp(cp, fixture, pp)
                r["cpp_exit"], r["cpp_last"] = cc, last
                if last == "YES":
                    failures.append(f"{name}: C++ accepted a mutated proof (the mutation does not reach a checked byte)")
            results.append(r)
            print(f"{name:52s} rust={r['rust_class']:16s} cpp={r.get('cpp_last', '-')}")
        for name, st in unbound:
            sp = d / "u.schedule"
            sp.write_text(st)
            code, so, se = walk(walk_bin, fixture / "example.proof", fixture, inputs, sp)
            r = {"case": name, "rust_exit": code, "rust_class": "NOT_BOUND_BY_MERKLE" if code == 0 else classify(se),
                 "expected": "accepted by the Merkle walk; D7 must derive it and D9 enforce it"}
            if code != 0:
                failures.append(f"{name}: expected the Merkle-only walk to be blind to this field; it rejected: update the test")
            results.append(r)
            print(f"{name:52s} rust={r['rust_class']:16s} (documented limitation)")
    if out:
        Path(out).write_text(json.dumps({"cases": results, "failures": failures}, indent=1))
    n_proof = sum(1 for c in cases if c[1] is not None)
    print(f"PROOF_NEGATIVE cases={len(results)} proof_mutations={n_proof} rust_rejected={sum(r['rust_exit'] != 0 for r in results)} "
          f"not_bound_by_merkle={len(unbound)} failures={len(failures)}")
    if failures:
        print("\n".join(failures))
        sys.exit(1)


def parse_openings(walk_bin, fixture, inputs, schedule):
    """Openings with geometry: the walk prints them with --list-openings."""
    c = fixture / "config"
    r = subprocess.run([str(walk_bin), str(fixture / "example.proof"), str(fixture / "example.req"), str(c / "policy.txt"),
                        str(c / "layout.txt"), str(c / "KL.bin"), str(inputs), str(schedule), "--list-openings", "yes"],
                       capture_output=True, text=True, timeout=300)
    if r.returncode != 0:
        raise SystemExit(r.stderr)
    out = []
    for l in r.stdout.splitlines():
        if l.startswith("opening "):
            f = dict(kv.split("=") for kv in l.split()[1:])
            out.append({k: (v if k == "chain" else int(v)) for k, v in f.items()})
    return out


if __name__ == "__main__":
    main()
