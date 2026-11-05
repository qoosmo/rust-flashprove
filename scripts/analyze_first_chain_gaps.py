#!/usr/bin/env python3
"""Locate unverified file-only proof bytes skipped by the transcript replay.

The report does not validate Merkle openings or other file-only records. It
only computes gaps in the observed transcript reads, and independently checks
the Rust gap byte count.
"""
import argparse
from pathlib import Path

ROUNDS = 8037

def main():
    p=argparse.ArgumentParser()
    p.add_argument("trace",type=Path)
    p.add_argument("proof",type=Path)
    p.add_argument("bulk_result",type=Path)
    a=p.parse_args()
    nproof=a.proof.stat().st_size
    if nproof>512*1024*1024:
        raise ValueError("proof exceeds instrumented audit limit")
    lines=a.trace.read_text().splitlines()
    data={}
    for line in lines:
        key,sep,val=line.partition("=")
        if not sep or key in data:
            raise ValueError("invalid or repeated trace entry")
        data[key]=val
    count=0
    skipped=0
    cursor=44
    first=[]
    rounds=set()
    def consume(key,round_number):
        nonlocal cursor,skipped,count
        remaining_s,length_s=data[key].split(",")
        remaining=int(remaining_s)
        length=int(length_s)
        start=nproof-remaining-length
        end=start+length
        if length<=0 or start<cursor or end>nproof:
            raise ValueError(f"non-monotone or invalid read {key}")
        if start>cursor:
            width=start-cursor
            skipped+=width
            count+=1
            rounds.add(round_number)
            if len(first)<12:
                first.append((round_number,cursor,width,key))
        cursor=end
    for round_number in range(1,ROUNDS+1):
        if f"bulk_{round_number}_rho" not in data:
            raise ValueError(f"missing transcript state for round {round_number}")
        i=0
        while True:
            key=f"bulk_{round_number}_piece_{i}"
            if key not in data:
                break
            consume(key,round_number)
            i+=1
        nonce=f"bulk_{round_number}_nonce_range"
        if nonce in data:
            consume(nonce,round_number)
    result={}
    for line in a.bulk_result.read_text().splitlines():
        if "=" in line:
            k,v=line.split("=",1)
            result[k]=v
    if result.get("BULK_FIRST_CHAIN_ROUNDS_OK") is not None:
        pass
    if result.get("rounds_replayed")!=str(ROUNDS):
        raise ValueError("replay count disagrees with trace")
    if result.get("file_only_gap_bytes_skipped")!=str(skipped):
        raise ValueError("gap count disagrees with independently replayed Rust")
    if result.get("last_observed_proof_offset")!=str(cursor):
        raise ValueError("final proof offset disagrees with Rust")
    print("FIRST_CHAIN_GAP_REPORT")
    print(f"transcript_rounds={ROUNDS}")
    print(f"gap_regions={count}")
    print(f"rounds_with_gaps={len(rounds)}")
    print(f"gap_bytes={skipped}")
    print(f"last_transcript_read_end={cursor}")
    print(f"proof_size={nproof}")
    for i,(round_no,at,width,key) in enumerate(first,1):
        print(f"gap_{i}=before_round_{round_no},offset_{at},bytes_{width},next_{key}")
    print("scope=GAP_LOCATOR_ONLY_CONTENT_NOT_VERIFIED")

if __name__=="__main__":
    main()
