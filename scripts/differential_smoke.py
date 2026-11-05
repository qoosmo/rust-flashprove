#!/usr/bin/env python3
"""C++/Rust pre-verification comparison on a pinned FlashProve corpus.

C++ validates the complete proof. Rust's inspect-bundle checks only the H821
headers and request/next-token envelope. This is NOT full-verifier differential
verification and must never be reported as semantic equivalence.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import subprocess
import sys
import tempfile
from dataclasses import asdict, dataclass
from pathlib import Path

PINNED_UPSTREAM = "9e2bdd8ff5bf9c62f18263d7dac189b0400b260c"

@dataclass(frozen=True)
class Case:
    name: str
    expected_cpp: str
    expected_rust_inspection: str
    description: str

CASES = (
    Case("honest", "YES", "STRUCTURAL_OK", "unaltered accepted-proof corpus"),
    Case("short-header", "NO", "STRUCTURAL_REJECT", "proof truncated to 11 bytes"),
    Case("wrong-tag", "NO", "STRUCTURAL_REJECT", "first proof tag byte changed"),
    Case("wrong-version", "NO", "STRUCTURAL_REJECT", "H821 version byte changed"),
    Case("body-bit-flip", "NO", "STRUCTURAL_OK", "byte flipped inside opaque proof body"),
    Case("trailing-byte", "NO", "STRUCTURAL_OK", "extra byte appended to proof body"),
)

def mutation(proof: bytes, name: str) -> bytes:
    if not proof.startswith(b"CPPFH821") or len(proof) <= 12:
        raise ValueError("expected a non-empty H821 proof")
    if name == "honest":
        return proof
    if name == "short-header":
        return proof[:11]
    if name == "wrong-tag":
        return b"X" + proof[1:]
    if name == "wrong-version":
        return proof[:4] + b"X" + proof[5:]
    if name == "body-bit-flip":
        changed = bytearray(proof)
        changed[(12 + len(proof)) // 2] ^= 1
        return bytes(changed)
    if name == "trailing-byte":
        return proof + b"\0"
    raise ValueError(f"unknown mutation: {name}")

def final_line(stdout: str) -> str:
    return next((line.strip() for line in reversed(stdout.splitlines()) if line.strip()), "")

def cpp_verdict(return_code: int, last_line: str) -> str:
    # Upstream: never search for YES in the middle of output.
    if return_code == 0 and (last_line == "YES" or last_line.startswith("WITHIN LIMITS:")):
        return "YES"
    if return_code == 1 and last_line.startswith("NO:"):
        return "NO"
    return "OTHER"

def rust_inspection(return_code: int, stdout: str) -> str:
    if return_code == 0 and "NOT VERIFIED:" in stdout:
        return "STRUCTURAL_OK"
    if return_code == 2:
        return "STRUCTURAL_REJECT"
    return "OTHER"

def execute(argv: list[str], timeout: int = 120) -> subprocess.CompletedProcess[str]:
    return subprocess.run(argv, capture_output=True, text=True, timeout=timeout, check=False)

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path, required=True)
    parser.add_argument("--cpp", type=Path, required=True)
    parser.add_argument("--rust", type=Path, required=True)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    upstream = args.upstream.resolve(strict=True)
    cpp = args.cpp.resolve(strict=True)
    rust = args.rust.resolve(strict=True)
    sha = execute(["git", "-C", str(upstream), "rev-parse", "HEAD"])
    if sha.returncode or sha.stdout.strip() != PINNED_UPSTREAM:
        print("ERROR: upstream checkout is not pinned to " + PINNED_UPSTREAM, file=sys.stderr)
        return 2

    fixture = upstream / "examples" / "accepted-proof"
    proof = (fixture / "example.proof").read_bytes()
    proof_hash = hashlib.sha256(proof).hexdigest()
    if proof_hash != "5ed47fd101093e826a5bc833e57633e5a9237b49213c8f37cf518a3c1c8d9d99":
        print("ERROR: accepted proof fixture differs from SHA256SUMS", file=sys.stderr)
        return 2
    config = fixture / "config"
    key = fixture / "ivk"
    request = fixture / "example.req"
    token = fixture / "example.y"
    identity = (fixture / "ID.txt").read_text().strip()
    if len(identity) != 64 or any(ch not in "0123456789abcdef" for ch in identity):
        print("ERROR: malformed upstream fixture ID", file=sys.stderr)
        return 2

    records = []
    with tempfile.TemporaryDirectory(prefix="rustflashprove-diff-") as scratch:
        for case in CASES:
            changed = Path(scratch) / (case.name + ".proof")
            changed.write_bytes(mutation(proof, case.name))
            cpp_run = execute([str(cpp), str(config), str(key), str(request),
                               str(token), str(changed), "-id", identity, "-q"])
            rust_run = execute([str(rust), "inspect-bundle",
                                str(config / "policy.txt"), str(request),
                                str(token), str(changed)])
            ending = final_line(cpp_run.stdout)
            c_verdict = cpp_verdict(cpp_run.returncode, ending)
            r_status = rust_inspection(rust_run.returncode, rust_run.stdout)
            passed = (c_verdict == case.expected_cpp and
                      r_status == case.expected_rust_inspection)
            records.append({
                **asdict(case),
                "cpp_exit": cpp_run.returncode,
                "cpp_last_line": ending,
                "cpp_verdict": c_verdict,
                "rust_exit": rust_run.returncode,
                "rust_status": r_status,
                "expected_behaviour_observed": passed,
            })
            tag = "PASS" if passed else "FAIL"
            print(f"[{tag}] {case.name}: C++={c_verdict} (exit {cpp_run.returncode}); "
                  f"Rust={r_status} (exit {rust_run.returncode})")
            if not passed:
                print("  C++ stdout tail:", cpp_run.stdout[-500:], file=sys.stderr)
                print("  C++ stderr tail:", cpp_run.stderr[-500:], file=sys.stderr)
                print("  Rust stderr tail:", rust_run.stderr[-500:], file=sys.stderr)

    passed = all(r["expected_behaviour_observed"] for r in records)
    report = {
        "kind": "PRE_VERIFICATION_SMOKE_ONLY",
        "full_rust_verification": False,
        "semantic_equivalence_established": False,
        "upstream_commit": PINNED_UPSTREAM,
        "proof_sha256": proof_hash,
        "cases": records,
        "passed": passed,
        "limitations": "Rust checks only proof headers, policy version, and request "
                       "envelope; it does not inspect the proof body or issue a proof verdict.",
    }
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print("RESULT: " + ("SMOKE PASSED" if passed else "SMOKE FAILED"))
    print("NOTE: this is NOT C++/Rust verifier equivalence.")
    return 0 if passed else 1

if __name__ == "__main__":
    sys.exit(main())
