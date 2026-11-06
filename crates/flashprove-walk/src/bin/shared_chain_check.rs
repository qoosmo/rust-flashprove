//! Algebraic checks of the shared chain, block by block, as far as they are ported.
//!
//! usage: shared_chain_check PROOF REQUEST POLICY LAYOUT SCALES FIRST_QUERY_DIR SCHEDULE [--compare-notes NOTES]
//!
//! Runs the native proof walk, then computes the values that upstream's own
//! block-by-block notes (`VerifierContext::notes`) record for the shared chain,
//! from the walk's draws and openings only. With --compare-notes, compares them
//! with upstream's (tests/vectors/accepted-proof.notes.txt) AFTER computing.
//! Ported so far: FOLDEQ (notes 0-4). Not a verdict: no block's claims are
//! tested yet; that happens at BASE.
use flashprove_field::{Ext3 as E, Fp};
use flashprove_iop::code::Codes;
use flashprove_iop::foldeq;
use flashprove_iop::shapes::LinShape;
use flashprove_transcript::first_query::parse_parameters;
use flashprove_walk::{
    parse_items, walk_proof, FirstQueryBytes, OpeningSchedule, ProofInputs,
    LABEL_PROOF_SHARED_CHAIN,
};
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
    let shared = w
        .chains
        .iter()
        .find(|c| c.label == LABEL_PROOF_SHARED_CHAIN)
        .ok_or("no shared chain")?;

    // The bound shapes, parsed canonically from the shared chain's own first query.
    let p3 = parse_parameters(&sp).map_err(|e| e.to_string())?;
    let item = |n: &str| {
        p3.items
            .iter()
            .find(|i| i.name == n)
            .map(|i| i.value.clone())
            .ok_or(format!("no parameter '{n}'"))
    };
    let codes = Codes::parse(&item("codes")?).map_err(|e| format!("codes: {e}"))?;
    let shape =
        LinShape::parse(&item("the test on the table")?).map_err(|e| format!("LIN shape: {e}"))?;
    if let Some(f) = shape.fault_with(&codes) {
        return Err(format!("LIN shape: {f}"));
    }
    let s3 = parse_items(&ss).map_err(|e| e.to_string())?;
    let table = &s3
        .iter()
        .find(|i| i.name == "table")
        .ok_or("no table item")?
        .value;
    let (root, record) =
        foldeq::parse_table_item(table, &shape.fold.index).map_err(|e| format!("table: {e}"))?;
    if root != w.table_root {
        return Err("the table item's root differs from the walk's".into());
    }

    // LIN point (round 1): psi in E^{k_col}; FOLDEQ folds the table at gamma = psi[k_lo..].
    let mut d = shared.draw(1).ok_or("no round 1")?;
    if shared.rounds[0].name != "LIN point" {
        return Err(format!(
            "round 1 is {}, not LIN point",
            shared.rounds[0].name
        ));
    }
    let psi: Vec<E> = (0..shape.k_col())
        .map(|_| d.extension())
        .collect::<Result<_, _>>()
        .map_err(|e| e.to_string())?;
    let gamma = &psi[shape.k_lo as usize..];

    // The stored-table opening (R8.7: read first after LOC) and its first draw.
    let stored = shared
        .openings
        .iter()
        .find(|o| o.stored)
        .ok_or("no stored opening")?;
    let x = *stored.draw_list.first().ok_or("empty list")?;
    let idx = stored
        .list
        .binary_search(&x)
        .map_err(|_| "first draw not in the list")?;
    let rows = shape.fold.index.rows() as usize;
    if stored.width != rows {
        return Err(format!(
            "stored opening has width {}, the table has {rows} rows",
            stored.width
        ));
    }
    let column: &[Fp] = &stored.columns[idx * rows..(idx + 1) * rows];
    let n = foldeq::notes(&shape.fold, gamma, &record, x, column);
    // LIN zeta (round 7): zeta in E^{k_row}; the claim (Fold) ties Omega to G_u.
    if shared.rounds[6].name != "LIN zeta" {
        return Err(format!(
            "round 7 is {}, not LIN zeta",
            shared.rounds[6].name
        ));
    }
    let mut dz = shared.draw(7).ok_or("no round 7")?;
    let zeta: Vec<E> = (0..shape.k_row())
        .map(|_| dz.extension())
        .collect::<Result<_, _>>()
        .map_err(|e| e.to_string())?;
    let ours = [
        ("FOLDEQ:_e_0", n.e_0),
        ("FOLDEQ:_(Rec_0)'s_target", n.rec_0_target),
        ("FOLDEQ:_(Col_1)'s_target", n.col_1_target),
        ("FOLDEQ:_(Col_1)_on_G_u<0>", n.col_1_on_u_message_0),
        ("FOLDEQ:_(Col_1)_on_G_u<B>", n.col_1_on_u_tail_0),
        (
            "LIN:_(Fold)_on_Omega<0>",
            flashprove_iop::lin::fold_on_omega(&shape, &zeta, 0),
        ),
        (
            "LIN:_(Fold)_on_G_u<1>",
            flashprove_iop::lin::fold_on_u(&shape, &psi, &zeta, 1),
        ),
    ];
    println!(
        "SHARED_CHAIN_CHECK walk=OK table_rows={rows} k_col={} k_lo={} first_draw={x}",
        shape.k_col(),
        shape.k_lo
    );
    for (i, (what, v)) in ours.iter().enumerate() {
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
        for (i, (what, v)) in ours.iter().enumerate() {
            let (cw, cv) = cpp.get(&i).ok_or(format!("C++ has no note {i}"))?;
            if cw != what || *cv != show(v) {
                return Err(format!(
                    "note {i} ({what}): Rust {} differs from C++ {cv}",
                    show(v)
                ));
            }
        }
        println!(
            "cpp_notes_compared={} of {} (FOLDEQ, LIN fold row: all equal)",
            ours.len(),
            cpp.len()
        );
    }
    println!("scope=VALUES_OF_PORTED_BLOCKS_ONLY_NOT_A_VERDICT ported=FOLDEQ,LIN_fold_row pending=SPLIT,BAT,FOLD,CS,BASE");
    Ok(())
}

fn main() {
    let args: Vec<String> = env::args().skip(1).collect();
    if let Err(e) = run(&args) {
        eprintln!("SHARED_CHAIN_CHECK_REJECT: {e}");
        std::process::exit(1);
    }
}
