//! Algebraic checks of the shared chain, block by block, as far as they are ported.
//!
//! usage: shared_chain_check PROOF REQUEST POLICY LAYOUT SCALES FIRST_QUERY_DIR SCHEDULE [--compare-notes NOTES]
//!
//! Runs the native proof walk, then computes the values that upstream's own
//! block-by-block notes (`VerifierContext::notes`) record for the shared chain,
//! from the walk's draws and openings only. With --compare-notes, compares them
//! with upstream's (tests/vectors/accepted-proof.notes.txt) AFTER computing.
//! All 45 notes: FOLDEQ, SEND, LIN, SPLIT, then for test_u and test_omega BAT, FOLD and CS
//! per stage, and BASE with its two refusals (the linear check and the encoding check). Not a verdict: no block's claims are
//! tested yet; that happens at BASE.
use flashprove_field::Ext3 as E;
use flashprove_walk::{walk_proof, FirstQueryBytes, OpeningSchedule, ProofInputs};
use std::collections::BTreeMap;
use std::{env, fs};

fn read(path: &str, limit: u64) -> Result<Vec<u8>, String> {
    let n = fs::metadata(path)
        .map_err(|e| format!("{path}: {e}"))?
        .len();
    if n > limit {
        return Err(format!("{path}: larger than {limit} bytes"));
    }
    fs::read(path).map_err(|e| format!("{path}: {e}"))
}
fn show(x: &E) -> String {
    format!("{},{},{}", x.0[0].value(), x.0[1].value(), x.0[2].value())
}

fn run(args: &[String]) -> Result<(), String> {
    let mut pos: Vec<&String> = Vec::new();
    let mut notes_path = None;
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--compare-notes" {
            notes_path = Some(it.next().ok_or("--compare-notes needs a file")?.clone());
        } else if a.starts_with("--") {
            return Err(format!("unknown option {a}"));
        } else {
            pos.push(a);
        }
    }
    if pos.len() != 7 {
        return Err("usage: shared_chain_check PROOF REQUEST POLICY LAYOUT SCALES FIRST_QUERY_DIR SCHEDULE [--compare-notes NOTES]".into());
    }
    let proof = read(pos[0], 512 << 20)?;
    let files: Vec<Vec<u8>> = (1..5)
        .map(|i| read(pos[i], 64 << 20))
        .collect::<Result<_, _>>()?;
    let q = |n: &str| read(&format!("{}/{n}", pos[5]), 16 << 20);
    let (fp, fs_, sp, ss, tp, ts) = (
        q("first-parameters.bin")?,
        q("first-statement.bin")?,
        q("shared-parameters.bin")?,
        q("shared-statement.bin")?,
        q("second-parameters.bin")?,
        q("second-statement.bin")?,
    );
    let schedule = OpeningSchedule::parse(
        &String::from_utf8(read(pos[6], 1 << 20)?).map_err(|_| "schedule is not UTF-8")?,
    )
    .map_err(|e| e.to_string())?;
    let w = walk_proof(
        &proof,
        &ProofInputs {
            request: &files[0],
            policy: &files[1],
            layout: &files[2],
            scales: &files[3],
            first: FirstQueryBytes {
                parameters: &fp,
                statement: &fs_,
            },
            shared: FirstQueryBytes {
                parameters: &sp,
                statement: &ss,
            },
            second: FirstQueryBytes {
                parameters: &tp,
                statement: &ts,
            },
            schedule: &schedule,
        },
    )
    .map_err(|e| format!("walk: {e}"))?;
    let all = flashprove_walk::shared_chain::shared_chain_notes(&proof, &w, &sp, &ss)?;
    println!("SHARED_CHAIN_ALGEBRA_OK both proximity tests end in BASE with both refusals passed");
    println!("SHARED_CHAIN_CHECK walk=OK notes={}", all.len());
    for (i, what, v) in &all {
        println!("note i={i} what={what} value={}", show(v));
    }
    if let Some(p) = notes_path {
        let text = String::from_utf8(read(&p, 64 << 20)?).map_err(|_| "notes not UTF-8")?;
        let mut cpp = BTreeMap::new();
        for l in text.lines() {
            let f: BTreeMap<&str, &str> = l
                .split_whitespace()
                .skip(1)
                .filter_map(|kv| kv.split_once('='))
                .collect();
            if f.get("chain") == Some(&"46524d03") {
                cpp.insert(
                    f["i"].parse::<usize>().map_err(|_| "bad note index")?,
                    (f["what"].to_string(), f["value"].to_string()),
                );
            }
        }
        for (i, what, v) in &all {
            let (cw, cv) = cpp.get(i).ok_or(format!("C++ has no note {i}"))?;
            if cw != what || *cv != show(v) {
                return Err(format!(
                    "note {i} ({what}): Rust {} differs from C++ {cv}",
                    show(v)
                ));
            }
        }
        println!(
            "cpp_notes_compared={} of {} (every block of both proximity tests through BASE: all equal)",
            all.len(),
            cpp.len()
        );
    }
    println!("scope=SHARED_CHAIN_ONLY ported=FOLDEQ,SEND,LIN_fold,SPLIT,BAT,FOLD,CS,BASE(test_u,test_omega) pending=first_chain,second_chain,verdict");
    Ok(())
}

fn main() {
    let args: Vec<String> = env::args().skip(1).collect();
    if let Err(e) = run(&args) {
        eprintln!("SHARED_CHAIN_CHECK_REJECT: {e}");
        std::process::exit(1);
    }
}
