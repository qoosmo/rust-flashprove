//! Native walk of a whole proof file: three chains, the place, every opening, to the last byte.
//!
//! usage: proof_walk PROOF REQUEST POLICY LAYOUT SCALES FIRST_QUERY_DIR SCHEDULE
//!        [--compare-chains LOG] [--compare-openings LOG]
//!
//! FIRST_QUERY_DIR holds {first,shared,second}-{parameters,statement}.bin: each
//! chain's serialized first query (stage D7 will derive these). The walk checks
//! them item by item: the first chain against the public files, the shared
//! chain's table, codes and binding root, the second chain's two seals.
//! SCHEDULE: which trees open after which positions round, their root source and
//! widths (stage D7 stand-in).
//!
//! The --compare-* files are the request stage's C++ diagnostics, read only
//! AFTER the walk has finished. They never feed it.
use flashprove_walk::{walk_proof, FirstQueryBytes, OpeningSchedule, ProofInputs, ProofWalk};
use std::collections::BTreeMap;
use std::{env, fs};

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
fn fields(line: &str) -> BTreeMap<&str, &str> {
    line.split_whitespace()
        .skip(1)
        .filter_map(|kv| kv.split_once('='))
        .collect()
}
fn num(f: &BTreeMap<&str, &str>, k: &str) -> Result<usize, String> {
    f.get(k)
        .and_then(|v| v.parse().ok())
        .ok_or(format!("C++ log: field {k}"))
}

/// (chain label, round) -> reads (piece or nonce, offset, size).
type Reads = BTreeMap<(String, usize), Vec<(String, usize, usize)>>;

fn compare_chains(w: &ProofWalk, len: usize, path: &str) -> Result<(usize, usize), String> {
    let text = String::from_utf8(read(path, 256 << 20)?).map_err(|_| "log is not UTF-8")?;
    let mut rounds = BTreeMap::new();
    let mut reads: Reads = BTreeMap::new();
    let mut starts = BTreeMap::new();
    let mut seals = BTreeMap::new();
    for line in text.lines() {
        let f = fields(line);
        match line.split(' ').next() {
            Some("round") => {
                rounds.insert(
                    (f["label"].to_string(), num(&f, "r")?),
                    (
                        f["name"].replace('_', " "),
                        num(&f, "kind")?,
                        f["rho"].to_string(),
                    ),
                );
            }
            Some(k @ ("piece" | "nonce")) => {
                let s = len - num(&f, "left")?;
                reads
                    .entry((f["label"].to_string(), num(&f, "r")?))
                    .or_default()
                    .push((k.to_string(), s, num(&f, "size")?));
            }
            Some("chain") => {
                starts.insert(f["label"].to_string(), len - num(&f, "left")?);
            }
            Some("seal") => {
                seals.insert(f["label"].to_string(), f["digest"].to_string());
            }
            _ => {}
        }
    }
    let mut compared = 0;
    for c in &w.chains {
        let lab = format!("{:x}", c.label);
        if starts.get(&lab) != Some(&c.start) {
            return Err(format!(
                "chain {lab}: C++ starts at {:?}, Rust at {}",
                starts.get(&lab),
                c.start
            ));
        }
        if seals.get(&lab).map(String::as_str) != c.seal.as_ref().map(|s| hex(s)).as_deref() {
            return Err(format!("chain {lab}: seal differs from C++"));
        }
        for r in &c.rounds {
            let (name, kind, rho) = rounds
                .get(&(lab.clone(), r.round as usize))
                .ok_or(format!("chain {lab} round {}: not in the C++ log", r.round))?;
            if *name != r.name || *kind != r.kind as usize || *rho != hex(&r.rho) {
                return Err(format!(
                    "chain {lab} round {}: name, kind or state differs from C++",
                    r.round
                ));
            }
            let mut at = r.message_offset;
            let mut nonce = None;
            for (k, s, n) in reads
                .get(&(lab.clone(), r.round as usize))
                .map(Vec::as_slice)
                .unwrap_or(&[])
            {
                if k == "nonce" {
                    nonce = Some(*s);
                    continue;
                }
                if *s != at {
                    return Err(format!(
                        "chain {lab} round {}: C++ read at {s}, Rust cursor at {at}",
                        r.round
                    ));
                }
                at += n;
            }
            if at != r.message_offset + r.message_bytes || nonce != r.nonce_offset {
                return Err(format!(
                    "chain {lab} round {}: message span or nonce offset differs from C++",
                    r.round
                ));
            }
            compared += 1;
        }
        if rounds.keys().filter(|(l, _)| *l == lab).count() != c.rounds.len() {
            return Err(format!("chain {lab}: C++ closed another number of rounds"));
        }
    }
    Ok((compared, w.chains.len()))
}

fn compare_openings(w: &ProofWalk, len: usize, path: &str) -> Result<usize, String> {
    let text = String::from_utf8(read(path, 64 << 20)?).map_err(|_| "log is not UTF-8")?;
    let cpp: Vec<_> = text.lines().map(fields).collect();
    let rust: Vec<_> = w.chains.iter().flat_map(|c| c.openings.iter()).collect();
    if cpp.len() != rust.len() {
        return Err(format!(
            "C++ read {} openings, Rust {}",
            cpp.len(),
            rust.len()
        ));
    }
    for (o, c) in rust.iter().zip(&cpp) {
        let start = len - num(c, "reader_left_before")?;
        let end = len - num(c, "reader_left_after")?;
        let list: Vec<u64> = c["list"]
            .split(',')
            .map(|x| x.parse().unwrap_or(u64::MAX))
            .collect();
        let checks = [
            ("offset", start == o.offset),
            ("length", end - start == o.bytes),
            ("tree", num(c, "tree")? as u32 == o.tree),
            ("stored", (c["stored"] == "1") == o.stored),
            ("root", c["root"] == hex(&o.root)),
            ("run", o.stored || c["run"] == hex(&o.run)),
            ("parameters", c["params"] == hex(&o.parameters)),
            ("list", list == o.list),
            ("C++ accepted", c["ok"] == "1" && c["checked"] == "1"),
        ];
        for (what, ok) in checks {
            if !ok {
                return Err(format!(
                    "opening of tree {} in chain {:x} after round {}: {what} differs from C++",
                    o.tree, o.chain, o.after_round
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
            if !matches!(
                a.as_str(),
                "--compare-chains" | "--compare-openings" | "--list-openings"
            ) || compare.insert(a.clone(), v.clone()).is_some()
            {
                return Err(format!("unknown or repeated option {a}"));
            }
        } else {
            pos.push(a);
        }
    }
    if pos.len() != 7 {
        return Err("usage: proof_walk PROOF REQUEST POLICY LAYOUT SCALES FIRST_QUERY_DIR SCHEDULE [--compare-chains L] [--compare-openings L]".into());
    }
    let proof = read(pos[0], 512 << 20)?;
    let request = read(pos[1], 16 << 20)?;
    let policy = read(pos[2], 16 << 20)?;
    let layout = read(pos[3], 16 << 20)?;
    let scales = read(pos[4], 64 << 20)?;
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
    let inputs = ProofInputs {
        policy: &policy,
        layout: &layout,
        scales: &scales,
        request: &request,
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
    };
    let w = walk_proof(&proof, &inputs).map_err(|e| e.to_string())?;

    println!("NATIVE_PROOF_WALK_OK");
    println!(
        "proof_bytes={} head=[0,12) stored_copy={}",
        proof.len(),
        w.copy
    );
    let mut opened_total = 0;
    let mut transcript_total = 0;
    let mut salts = 0;
    for c in &w.chains {
        let opened: usize = c.openings.iter().map(|o| o.bytes).sum();
        let transcript: usize = c
            .rounds
            .iter()
            .map(|r| r.message_bytes + if r.nonce_offset.is_some() { 8 } else { 0 })
            .sum();
        let salt = if c.salt_in_proof { 32 } else { 0 };
        opened_total += opened;
        transcript_total += transcript;
        salts += salt;
        println!(
            "chain {:x}: span=[{},{}) salt_in_proof={} rounds={} roots={} openings={} opened_bytes={} transcript_bytes={} seal={}",
            c.label,
            c.start,
            c.end,
            c.salt_in_proof,
            c.rounds.len(),
            c.roots.len(),
            c.openings.len(),
            opened,
            transcript,
            c.seal.map(|s| hex(&s)).unwrap_or_else(|| "-".into())
        );
        if c.end - c.start != salt + opened + transcript {
            return Err(format!(
                "chain {:x}: span is not exactly its salt, transcript and openings",
                c.label
            ));
        }
    }
    let place = w.place_span.1 - w.place_span.0;
    println!(
        "place: span=[{},{}) place={} binding_root={}",
        w.place_span.0,
        w.place_span.1,
        w.place,
        hex(&w.binding_root)
    );
    println!(
        "table_root={} (from the first query's table item)",
        hex(&w.table_root)
    );
    println!("merkle_vertices_recorded={}", w.merkle_vertices);
    let accounted = 12 + salts + transcript_total + opened_total + place;
    println!("bytes: head 12 + salts {salts} + transcript {transcript_total} + openings {opened_total} + place {place} = {accounted}");
    println!("unaccounted_bytes={}", proof.len() - accounted);
    if compare.get("--list-openings").map(String::as_str) == Some("yes") {
        for c in &w.chains {
            for o in &c.openings {
                println!("opening chain={:x} after_round={} tree={} offset={} bytes={} positions={} given={} salt={}", o.chain, o.after_round, o.tree, o.offset, o.bytes, o.list.len(), o.given, o.salt_bytes);
            }
        }
    }
    if accounted != proof.len() {
        return Err("the walk does not account for every byte".into());
    }
    // The shared chain, algebraically (D7 + D9): every block through BASE's two refusals.
    let notes = flashprove_walk::shared_chain::shared_chain_notes(&proof, &w, &sp, &ss)
        .map_err(|e| format!("shared chain: {e}"))?;
    println!("SHARED_CHAIN_VERIFIED notes={} (FOLDEQ, SEND, LIN, SPLIT, BAT, FOLD, CS, BASE of test_u and test_omega)", notes.len());
    if let Some(p) = compare.get("--compare-chains") {
        let (r, c) = compare_chains(&w, proof.len(), p)?;
        println!("cpp_chains_compared={c} rounds={r} (starts, seals, names, kinds, states, read offsets, nonces: all equal)");
    }
    if let Some(p) = compare.get("--compare-openings") {
        println!("cpp_openings_compared={} (offsets, lengths, trees, roots, runs, parameters, lists: all equal)", compare_openings(&w, proof.len(), p)?);
    }
    println!("independence=NO_CPP_OFFSETS_OR_TRACE_INPUTS; non-native inputs: first-query bytes (checked item by item), opening schedule (D7)");
    println!("scope=ALL_CHAINS_TRANSCRIPT_LINKAGE_AND_MERKLE_MEMBERSHIP_TO_EOF_SHARED_CHAIN_ALGEBRA_NOT_A_VERDICT pending=first_chain,second_chain");
    Ok(())
}

fn main() {
    let args: Vec<String> = env::args().skip(1).collect();
    if let Err(e) = run(&args) {
        eprintln!("PROOF_WALK_REJECT: {e}");
        std::process::exit(1);
    }
}
