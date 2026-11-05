#!/usr/bin/env python3
"""Fail-closed tests for the *trace-bound first-two-round replay*, not proof verification."""
from __future__ import annotations
import argparse
import subprocess
import tempfile
from pathlib import Path

def fail_if_accepted(executable: Path, proof: Path, trace: Path, case: str) -> None:
    result = subprocess.run([str(executable), str(proof), str(trace)], capture_output=True, text=True, timeout=90)
    if result.returncode == 0 or "REAL_FIRST_ROUND_MISMATCH:" not in result.stderr:
        raise RuntimeError(
            f"{case} was not rejected as a trace mismatch; code {result.returncode}\n"
            f"stdout={result.stdout[-600:]}\nstderr={result.stderr[-600:]}"
        )
    print(f"[PASS] corrupted {case} was rejected by Rust trace replay")

def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("rust", type=Path)
    p.add_argument("proof", type=Path)
    p.add_argument("trace", type=Path)
    args = p.parse_args()
    exe = args.rust.resolve(strict=True)
    proof_file = args.proof.resolve(strict=True)
    trace_file = args.trace.resolve(strict=True)
    base = proof_file.read_bytes()
    text = trace_file.read_text()
    fields = dict(line.split("=", 1) for line in text.splitlines())
    if len(fields) != len(text.splitlines()):
        raise RuntimeError("original C++ trace has duplicate keys")
    if len(base) < 60 or not base.startswith(b"CPPFH821"):
        raise RuntimeError("invalid original proof")
    baseline = subprocess.run([str(exe), str(proof_file), str(trace_file)], capture_output=True, text=True, timeout=90)
    if baseline.returncode != 0 or "REAL_FIRST_TWO_ROUNDS_OK" not in baseline.stdout:
        raise RuntimeError("valid real-round baseline fails")
    with tempfile.TemporaryDirectory(prefix="flashprove-negative-first-two-") as d:
        tmp = Path(d)
        first = 44
        second = first + int(fields["first_round_message_bytes"])
        if int(fields["first_round_work"]) > 0:
            second += int(fields["first_round_nonce_bytes"])
        mutate_at = [
            ("first-chain salt", 12),
            ("first-round prover message", first),
        ]
        if int(fields["second_round_message_bytes"]) > 0:
            mutate_at.append(("second-round prover message", second))
        for name, position in mutate_at:
            altered = bytearray(base)
            altered[position] ^= 1
            target = tmp / "changed.proof"
            target.write_bytes(altered)
            fail_if_accepted(exe, target, trace_file, name)
        shorter = tmp / "truncated.proof"
        shorter.write_bytes(base[:second + max(0, int(fields["second_round_message_bytes"]) - 1)])
        fail_if_accepted(exe, shorter, trace_file, "second-round truncation")
        line = next(x for x in text.splitlines() if x.startswith("first_parameters_serialized="))
        bad = line[:-1] + ("0" if line[-1] != "0" else "1")
        altered_trace = tmp / "changed.trace"
        altered_trace.write_text(text.replace(line, bad))
        fail_if_accepted(exe, proof_file, altered_trace, "parameter encoding")
    print("ALL REAL-ROUND NEGATIVE REPLAYS REJECTED")

if __name__ == "__main__":
    main()
