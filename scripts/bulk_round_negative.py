#!/usr/bin/env python3
"""Fail-closed mutation checks for the trace-guided 64-round replay."""
import argparse
import subprocess
import tempfile
from pathlib import Path

def run(exe, files):
    return subprocess.run([str(exe), *map(str, files)], capture_output=True, text=True, timeout=120)

def expect_reject(exe, files, name):
    r = run(exe, files)
    if r.returncode == 0 or "BULK_ROUND_REPLAY_REJECT:" not in r.stderr:
        raise RuntimeError(f"{name} was not rejected: {r.returncode} {r.stderr[-350:]}")
    print("[PASS] bulk replay rejected", name)

def main():
    p=argparse.ArgumentParser()
    for name in ["exe","trace","proof","request","policy","layout","scales"]:
        p.add_argument(name,type=Path)
    a=p.parse_args()
    exe=a.exe.resolve(strict=True)
    files=[getattr(a,k).resolve(strict=True) for k in
           ["trace","proof","request","policy","layout","scales"]]
    baseline=run(exe,files)
    if baseline.returncode!=0 or "BULK_FIRST_CHAIN_ROUNDS_OK" not in baseline.stdout:
        raise RuntimeError("baseline bulk replay not valid: "+baseline.stderr[-800:])
    with tempfile.TemporaryDirectory(prefix="flashprove-bulk-negative-") as d:
        work=Path(d)
        proof=bytearray(files[1].read_bytes())
        proof[44]^=1
        changed=work/"changed.proof";changed.write_bytes(proof)
        f=files.copy();f[1]=changed
        expect_reject(exe,f,"first-round proof message byte")
        trace=files[0].read_text()
        for key in ["bulk_3_rho","bulk_64_msg_hash"]:
            line=next(x for x in trace.splitlines() if x.startswith(key+"="))
            new=line[:-1]+("1" if line[-1]!="1" else "0")
            modified=work/(key+".trace")
            modified.write_text(trace.replace(line,new))
            f=files.copy();f[0]=modified
            expect_reject(exe,f,key)
        piece=next((x for x in trace.splitlines()
                    if x.startswith("bulk_") and "_piece_0=" in x and
                    3<=int(x.split("_")[1])<=64),None)
        if piece is None:
            raise RuntimeError("no proof message read event after second round")
        head, numbers=piece.split("=",1)
        remaining,size=map(int,numbers.split(","))
        modified=work/"offset.trace"
        modified.write_text(trace.replace(piece,head+"="+str(remaining)+","+str(size+1)))
        f=files.copy();f[0]=modified
        expect_reject(exe,f,"corrupted field length or read offset")
    print("ALL FOUR BULK TRACE MUTATIONS REJECTED")
if __name__=="__main__":
    main()
