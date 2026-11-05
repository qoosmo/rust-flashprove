#!/usr/bin/env python3
"""Real first-query audit: independent public file binding negative tests."""
import argparse
import subprocess
import tempfile
from pathlib import Path

def run(exe, files):
    return subprocess.run([str(exe), *map(str, files)], capture_output=True, text=True, timeout=90)

def main():
    p = argparse.ArgumentParser()
    for key in ["audit", "trace", "proof", "request", "policy", "layout", "scales"]:
        p.add_argument(key, type=Path)
    a = p.parse_args()
    exe = a.audit.resolve(strict=True)
    inputs = [getattr(a, n).resolve(strict=True) for n in
              ["trace", "proof", "request", "policy", "layout", "scales"]]
    baseline = run(exe, inputs)
    if baseline.returncode != 0 or "REAL_PUBLIC_QUERY_OK" not in baseline.stdout:
        raise RuntimeError("baseline public-query audit failed: " + baseline.stderr[-1000:])
    with tempfile.TemporaryDirectory(prefix="flashprove-public-query-") as temp:
        work = Path(temp)
        for position, title in [(2, "request"), (3, "policy"), (4, "layout"), (5, "scales")]:
            b = bytearray(inputs[position].read_bytes())
            if not b:
                raise RuntimeError(title + " is empty")
            b[len(b)//2] ^= 1
            mutated = work / ("changed-" + title)
            mutated.write_bytes(b)
            files = inputs.copy()
            files[position] = mutated
            check = run(exe, files)
            if check.returncode == 0 or "REAL_PUBLIC_QUERY_REJECT:" not in check.stderr:
                raise RuntimeError(title + " mutation did not fail closed")
            print("[PASS] changed", title, "rejected")
        proof = bytearray(inputs[1].read_bytes())
        if not proof.startswith(b"CPPFH821"):
            raise RuntimeError("invalid proof fixture")
        proof[8] ^= 1
        changed = work / "changed-copy.proof"
        changed.write_bytes(proof)
        files = inputs.copy()
        files[1] = changed
        check = run(exe, files)
        if check.returncode == 0 or "REAL_PUBLIC_QUERY_REJECT:" not in check.stderr:
            raise RuntimeError("copy index mutation did not fail closed")
        print("[PASS] changed proof copy index rejected")
        txt = inputs[0].read_text()
        line = next(l for l in txt.splitlines() if l.startswith("first_parameters_serialized="))
        mutated_line = line[:-1] + ("0" if line[-1] != "0" else "1")
        changed = work / "changed-parameters.trace"
        changed.write_text(txt.replace(line, mutated_line))
        files = inputs.copy()
        files[0] = changed
        check = run(exe, files)
        if check.returncode == 0 or "REAL_PUBLIC_QUERY_REJECT:" not in check.stderr:
            raise RuntimeError("parameter serialization mutation did not fail closed")
        print("[PASS] changed serialized parameters rejected")
    print("ALL SIX PUBLIC-INPUT MUTATIONS REJECTED")

if __name__ == "__main__":
    main()
