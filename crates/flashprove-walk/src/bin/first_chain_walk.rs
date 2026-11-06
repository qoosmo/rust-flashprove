//! Native walk of the first chain of a proof, with every Merkle opening verified.
//!
//! usage: first_chain_walk PROOF REQUEST POLICY LAYOUT SCALES FIRST_PARAMETERS FIRST_STATEMENT SCHEDULE
//!        [--compare-trace TRACE] [--compare-openings LOG]
//!
//! FIRST_PARAMETERS / FIRST_STATEMENT: the first query's serialized parameters
//! and statement (binary). They are audited against the public files here;
//! deriving them natively is stage D7. SCHEDULE: which trees open after which
//! positions round, with column widths (stage D7 stand-in).
//!
//! The --compare-* files are C++ diagnostics, read only AFTER the walk has
//! finished, to compare offsets, states, lists and roots. They never feed it.
use flashprove_transcript::configuration_digest;
use flashprove_transcript::first_query::{audit, parameters_digest};
use flashprove_walk::{read_head, walk_first_chain, ChainInputs, ChainWalk, OpeningSchedule};
use std::collections::BTreeMap;
use std::{env, fs};

const FIRST_LABEL: u64 = 0x4652_4d01;

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}
fn read(path: &str, limit: u64) -> Result<Vec<u8>, String> {
    let n = fs::metadata(path)
        .map_err(|e| format!("{path}: {e}"))?
        .len();
    if n > limit {
        return Err(format!("{path}: larger than {limit} bytes"));
    }
    fs::read(path).map_err(|e| format!("{path}: {e}"))
}

fn compare_trace(w: &ChainWalk, proof_len: usize, path: &str) -> Result<usize, String> {
    let text = String::from_utf8(read(path, 64 << 20)?).map_err(|_| "trace is not UTF-8")?;
    let mut t = BTreeMap::new();
    for line in text.lines() {
        if let Some((k, v)) = line.split_once('=') {
            t.insert(k.to_string(), v.to_string());
        }
    }
    let mut compared = 0;
    for r in &w.rounds {
        let k = |s: &str| format!("bulk_{}_{s}", r.round);
        let Some(rho) = t.get(&k("rho")) else {
            continue;
        };
        if *rho != hex(&r.rho) {
            return Err(format!("round {}: Rust rho differs from C++", r.round));
        }
        if t.get(&k("name")).map(String::as_str) != Some(r.name.as_str()) {
            return Err(format!("round {}: name differs", r.round));
        }
        if t.get(&k("kind")).and_then(|s| s.parse::<u8>().ok()) != Some(r.kind as u8) {
            return Err(format!(
                "round {}: Rust kind from R14.11 differs from C++ wire kind",
                r.round
            ));
        }
        // Message pieces: C++ reads each as (bytes left before the end, length).
        let mut i = 0;
        let mut at = r.message_offset;
        while let Some(spec) = t.get(&k(&format!("piece_{i}"))) {
            let (left, len) = spec.split_once(',').ok_or("bad piece")?;
            let left: usize = left.parse().map_err(|_| "bad piece")?;
            let len: usize = len.parse().map_err(|_| "bad piece")?;
            let start = proof_len
                .checked_sub(left)
                .and_then(|e| e.checked_sub(len))
                .ok_or("bad piece")?;
            if start != at {
                return Err(format!(
                    "round {}: piece {i} at {start}, Rust cursor at {at}",
                    r.round
                ));
            }
            at += len;
            i += 1;
        }
        if at != r.message_offset + r.message_bytes {
            return Err(format!(
                "round {}: C++ pieces cover {} bytes, plan says {}",
                r.round,
                at - r.message_offset,
                r.message_bytes
            ));
        }
        if let Some(spec) = t.get(&k("nonce_range")) {
            let (left, len) = spec.split_once(',').ok_or("bad nonce range")?;
            let start = proof_len
                - left.parse::<usize>().map_err(|_| "bad")?
                - len.parse::<usize>().map_err(|_| "bad")?;
            if Some(start) != r.nonce_offset {
                return Err(format!(
                    "round {}: nonce at {start}, Rust read it at {:?}",
                    r.round, r.nonce_offset
                ));
            }
        } else if r.nonce_offset.is_some() {
            return Err(format!(
                "round {}: Rust read a nonce that C++ did not",
                r.round
            ));
        }
        compared += 1;
    }
    Ok(compared)
}

fn compare_openings(w: &ChainWalk, proof_len: usize, path: &str) -> Result<usize, String> {
    let text = String::from_utf8(read(path, 64 << 20)?).map_err(|_| "log is not UTF-8")?;
    let label = format!("{:x}", w.label);
    let mut cpp = Vec::new();
    for line in text.lines() {
        let f: BTreeMap<&str, &str> = line
            .split_whitespace()
            .skip(1)
            .filter_map(|kv| kv.split_once('='))
            .collect();
        if f.get("chain") == Some(&label.as_str()) {
            cpp.push(f);
        }
    }
    if cpp.len() != w.openings.len() {
        return Err(format!(
            "C++ read {} openings in this chain, Rust {}",
            cpp.len(),
            w.openings.len()
        ));
    }
    for (o, c) in w.openings.iter().zip(&cpp) {
        let num = |k: &str| {
            c.get(k)
                .and_then(|v| v.parse::<usize>().ok())
                .ok_or(format!("C++ field {k}"))
        };
        let start = proof_len - num("reader_left_before")?;
        let end = proof_len - num("reader_left_after")?;
        let list: Vec<u64> = c["list"]
            .split(',')
            .map(|x| x.parse().unwrap_or(u64::MAX))
            .collect();
        let checks = [
            ("offset", start == o.offset),
            ("length", end - start == o.bytes),
            ("round", num("round")? as u64 == o.after_round),
            ("tree", num("tree")? as u32 == o.tree),
            ("root", c["root"] == hex(&o.root)),
            ("run", c["run"] == hex(&o.run)),
            ("parameters", c["params"] == hex(&o.parameters)),
            ("list", list == o.list),
            ("C++ accepted", c["ok"] == "1" && c["checked"] == "1"),
            ("stored", c["stored"] == "0"),
        ];
        for (what, ok) in checks {
            if !ok {
                return Err(format!(
                    "opening of tree {} after round {}: {what} differs from C++",
                    o.tree, o.after_round
                ));
            }
        }
    }
    Ok(cpp.len())
}

fn run(args: &[String]) -> Result<(), String> {
    let mut pos: Vec<&String> = Vec::new();
    let mut compare = BTreeMap::new();
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a.starts_with("--") {
            let v = it.next().ok_or(format!("{a} needs a value"))?;
            if !matches!(a.as_str(), "--compare-trace" | "--compare-openings")
                || compare.insert(a.clone(), v.clone()).is_some()
            {
                return Err(format!("unknown or repeated option {a}"));
            }
        } else {
            pos.push(a);
        }
    }
    if pos.len() != 8 {
        return Err("usage: first_chain_walk PROOF REQUEST POLICY LAYOUT SCALES FIRST_PARAMETERS FIRST_STATEMENT SCHEDULE [--compare-trace T] [--compare-openings L]".into());
    }
    let proof = read(pos[0], 512 << 20)?;
    let request = read(pos[1], 16 << 20)?;
    let policy = read(pos[2], 16 << 20)?;
    let layout = read(pos[3], 16 << 20)?;
    let scales = read(pos[4], 64 << 20)?;
    let pbytes = read(pos[5], 16 << 20)?;
    let sbytes = read(pos[6], 16 << 20)?;
    let schedule = OpeningSchedule::parse(
        &String::from_utf8(read(pos[7], 1 << 20)?).map_err(|_| "schedule is not UTF-8")?,
    )
    .map_err(|e| e.to_string())?;

    let (copy, _) = read_head(&proof).map_err(|e| e.to_string())?;
    let plan = audit(
        &pbytes,
        &sbytes,
        [&policy, &layout, &scales],
        &request,
        copy,
    )
    .map_err(|e| format!("first-query audit: {e}"))?;
    let pd = parameters_digest(&pbytes).map_err(|e| e.to_string())?;
    let configuration =
        configuration_digest(&[&policy, &layout, &scales]).map_err(|e| e.to_string())?;
    let inputs = ChainInputs {
        label: FIRST_LABEL,
        plan: &plan,
        parameters_digest: pd,
        statement: &sbytes,
        configuration,
        schedule: &schedule,
    };
    let w = walk_first_chain(&proof, &inputs).map_err(|e| e.to_string())?;

    let opened: usize = w.openings.iter().map(|o| o.bytes).sum();
    let transcript: usize = w
        .rounds
        .iter()
        .map(|r| r.message_bytes + r.nonce_offset.map_or(0, |_| plan.nonce_bytes as usize))
        .sum();
    println!("NATIVE_FIRST_CHAIN_WALK_OK");
    println!("rounds_walked={}", w.rounds.len());
    println!("roots_received={}", w.roots.len());
    println!("openings_verified={}", w.openings.len());
    println!("opened_bytes_verified={opened}");
    println!("transcript_bytes={transcript}");
    println!("chain_span=[44,{})", w.end);
    println!(
        "unaccounted_bytes_in_span={}",
        w.end - 44 - opened - transcript
    );
    println!("merkle_vertices_recorded={}", w.merkle_vertices);
    println!(
        "rho_after_last_round={}",
        hex(&w.rounds.last().map(|r| r.rho).unwrap_or(w.rho0))
    );
    println!("proof_bytes_after_chain={}", proof.len() - w.end);
    for o in &w.openings {
        println!(
            "opening after_round={} tree={} offset={} bytes={} positions={} draws={} given={}",
            o.after_round,
            o.tree,
            o.offset,
            o.bytes,
            o.list.len(),
            o.draws,
            o.given
        );
    }
    if w.end - 44 != opened + transcript {
        return Err("the chain's span is not exactly its transcript bytes and openings".into());
    }
    if let Some(p) = compare.get("--compare-trace") {
        println!(
            "cpp_trace_rounds_compared={} (offsets, pieces, nonces, names, kinds, rho: all equal)",
            compare_trace(&w, proof.len(), p)?
        );
    }
    if let Some(p) = compare.get("--compare-openings") {
        println!("cpp_openings_compared={} (offsets, lengths, trees, roots, run, parameters, lists: all equal)", compare_openings(&w, proof.len(), p)?);
    }
    println!("independence=NO_CPP_OFFSETS_OR_TRACE_INPUTS; non-native inputs: first-query bytes (audited), opening schedule (D7)");
    println!(
        "scope=FIRST_CHAIN_TRANSCRIPT_AND_MERKLE_MEMBERSHIP_NOT_ALGEBRAIC_CHECKS_NOT_A_VERDICT"
    );
    Ok(())
}

fn main() {
    let args: Vec<String> = env::args().skip(1).collect();
    if let Err(e) = run(&args) {
        eprintln!("FIRST_CHAIN_WALK_REJECT: {e}");
        std::process::exit(1);
    }
}
