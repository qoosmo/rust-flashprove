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
use flashprove_field::{Ext3 as E, Fp};
use flashprove_iop::claims;
use flashprove_iop::code::Codes;
use flashprove_iop::fold;
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
    // BAT on G_u's group: x from round 9; claims in begin_run() order.
    let msg = |r: usize| -> &[u8] {
        let rr = &shared.rounds[r - 1];
        &proof[rr.message_offset..rr.message_offset + rr.message_bytes]
    };
    for (r, name) in [
        (3, "SEND answer"),
        (6, "SEND answer"),
        (8, "SPLIT"),
        (9, "BAT"),
    ] {
        if shared.rounds[r - 1].name != name {
            return Err(format!(
                "round {r} is {}, not {name}",
                shared.rounds[r - 1].name
            ));
        }
    }
    // G_u's group: FOLDEQ's (Rec_i) then (Col) per draw; SPLIT's share of (Fold); the
    // sample claims of its members G_u (round 3) and the shared split's mask (round 6,
    // after Omega's answers). BAT (round 9) takes them in begin_run() order.
    let u_answers = claims::elements(msg(3))?;
    let omega_split_answers = claims::elements(msg(6))?;
    let a_omega = shape.omega.answers as usize;
    if u_answers.len() != shape.fold.u.answers as usize
        || omega_split_answers.len() != a_omega + shape.shared_split.answers as usize
    {
        return Err("a SEND answer message holds another number of answers than the shapes".into());
    }
    let share = match claims::elements(msg(8))?.as_slice() {
        [s] => *s,
        _ => return Err("SPLIT sends exactly one element".into()),
    };
    let eq_gamma = foldeq::weights(&shape.fold, gamma);
    let mut group_u = claims::GroupClaims::default();
    for i in 0..shape.fold.index.answers {
        group_u.add(
            claims::Kind::Plain,
            format!("FOLDEQ: (Rec_{i})"),
            foldeq::record_target(&shape.fold.index, &record, i, &eq_gamma),
        )?;
    }
    for (k, &dx) in stored.draw_list.iter().enumerate() {
        let at = stored
            .list
            .binary_search(&dx)
            .map_err(|_| "a draw not in the list")?;
        group_u.add(
            claims::Kind::Generator,
            format!("FOLDEQ: (Col_{})", k + 1),
            foldeq::column_symbol(&eq_gamma, &stored.columns[at * rows..(at + 1) * rows]),
        )?;
    }
    group_u.add_member_samples("G_u", &u_answers)?;
    let (omega_share, u_share) = claims::split_targets(E::ZERO, share); // (Fold) has target 0
    group_u.add(claims::Kind::Plain, "LIN: (Fold), second share", u_share)?;
    group_u.add_member_samples("shared split mask", &omega_split_answers[a_omega..])?;
    let bat_claims = group_u.begin_run()?;
    // Omega's group: SPLIT's first share; the samples of Omega and of the split mask
    // (round 6, as sent). Its test's BAT is round 27.
    if shared.rounds[26].name != "BAT" {
        return Err(format!("round 27 is {}, not BAT", shared.rounds[26].name));
    }
    let mut group_omega = claims::GroupClaims::default();
    group_omega.add(claims::Kind::Plain, "LIN: (Fold), first share", omega_share)?;
    group_omega.add_member_samples("Omega", &omega_split_answers[..a_omega])?;
    group_omega.add_member_samples("shared split mask", &omega_split_answers[a_omega..])?;
    let omega_claims = group_omega.begin_run()?;
    let mut d27 = shared.draw(27).ok_or("no round 27")?;
    let bat_omega =
        claims::batch_target(&omega_claims, d27.extension().map_err(|e| e.to_string())?);
    let mut d9 = shared.draw(9).ok_or("no round 9")?;
    let bat_u = claims::batch_target(&bat_claims, d9.extension().map_err(|e| e.to_string())?);
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
        ("BAT:_target", bat_u),
    ];
    // Upstream note index, name, value.
    let mut all: Vec<(usize, &str, E)> = ours
        .iter()
        .enumerate()
        .map(|(i, (w, v))| (i, *w, *v))
        .collect();
    all.push((26, "BAT:_target", bat_omega));
    // FOLD (fold_start_verify, fold_rounds_verify): the FOLD epsilon round's message ends with
    // the hiding sum (after the fresh mask's root when the mask was not sent ahead), its draw is
    // eps; then k FOLD rounds, each (c0, c2) then g. The running claim starts at sum + eps * t.
    let fold_target = |eps_round: usize, k: u32, target: E| -> Result<(E, Vec<E>), String> {
        let rr = &shared.rounds[eps_round - 1];
        if rr.name != "FOLD epsilon" {
            return Err(format!(
                "round {eps_round} is {}, not FOLD epsilon",
                rr.name
            ));
        }
        let m = msg(eps_round);
        let sum = match m.len().checked_sub(24) {
            Some(at) => match claims::elements(&m[at..])?.as_slice() {
                [x] => *x,
                _ => return Err("FOLD epsilon: no hiding sum".into()),
            },
            None => return Err("FOLD epsilon: no hiding sum".into()),
        };
        let mut de = shared
            .draw(eps_round as u64)
            .ok_or("no FOLD epsilon draw")?;
        let eps = de.extension().map_err(|e| e.to_string())?;
        let mut claim = fold::FoldVerifierRounds::new(sum, eps, target);
        let mut gamma = Vec::new();
        for j in 0..k as usize {
            let r = eps_round + 1 + j;
            if shared.rounds[r - 1].name != "FOLD round" {
                return Err(format!(
                    "round {r} is {}, not FOLD round",
                    shared.rounds[r - 1].name
                ));
            }
            let (c0, c2) = match claims::elements(msg(r))?.as_slice() {
                [c0, c2] => (*c0, *c2),
                _ => return Err(format!("FOLD round {r} sends exactly two elements")),
            };
            let mut dg = shared.draw(r as u64).ok_or("no FOLD round draw")?;
            let g = dg.extension().map_err(|e| e.to_string())?;
            claim.round(c0, c2, g);
            gamma.push(g);
        }
        if shared.rounds[eps_round + k as usize].name == "FOLD round" {
            return Err("more FOLD rounds than the stage's k".into());
        }
        Ok((claim.claim(), gamma))
    };
    let ku = shape.test_u.first().ok_or("test_u has no stage")?.k;
    let ko = shape.test_omega.first().ok_or("test_omega has no stage")?.k;
    let (fold_u, gamma_u) = fold_target(10, ku, bat_u)?;
    let (fold_o, gamma_o) = fold_target(28, ko, bat_omega)?;
    all.push((8, "FOLD:_target", fold_u));
    all.push((27, "FOLD:_target", fold_o));
    // CS (switch_verify, single_rows_symbols): the single rows' symbols at the CS round's first
    // draw x. Each group has one main member (rows over E, from row 0) and one old mask row
    // (h = 0); the fresh fold mask is the third row. A tree with log_n below the list's is read
    // at x mod 2^log_n (short_position).
    let opened = |after: u64, tree: u32| {
        shared
            .openings
            .iter()
            .find(|o| o.after_round == after && o.tree == tree)
            .ok_or(format!("no opening of tree {tree} after round {after}"))
    };
    let symbols =
        |after: u64, tree: u32, x: u64, from: usize, n: usize| -> Result<Vec<E>, String> {
            let o = opened(after, tree)?;
            let at = o.list.iter().position(|&p| p == x).ok_or(format!(
                "position {x} not in the list of tree {tree} after round {after}"
            ))?;
            let col = &o.columns[at * o.width..(at + 1) * o.width];
            if from + 3 * n > o.width {
                return Err(format!(
                    "tree {tree}: the column is narrower than the rows read"
                ));
            }
            Ok((0..n)
                .map(|b| {
                    E([
                        col[from + 3 * b],
                        col[from + 3 * b + 1],
                        col[from + 3 * b + 2],
                    ])
                })
                .collect())
        };
    // (CS round, k, h, gamma, main tree and its main rows, old mask tree, fresh tree and offset)
    let cs_y = |cs: u64,
                k: u32,
                h: u32,
                gamma: &[E],
                main: (u32, usize),
                old: u32,
                fresh: (u32, usize),
                logs: (u32, u32, u32)|
     -> Result<[E; 3], String> {
        if h != 0 {
            return Err("CS: only h = 0 is ported (one old mask row)".into());
        }
        let x = *opened(cs, main.0)?.draw_list.first().ok_or("CS: no draw")?;
        let short = |lg: u32| x & ((1_u64 << lg) - 1);
        let mut rows = symbols(cs, main.0, short(logs.0), 0, main.1)?;
        rows.resize(1 << k, E::ZERO);
        let y_main = fold::fold_low(rows, gamma, k)[0];
        let y_0 = symbols(cs, old, short(logs.1), 0, 1)?[0];
        let y_1 = symbols(cs, fresh.0, short(logs.2), fresh.1, 1)?[0];
        Ok([y_main, y_0, y_1])
    };
    // test_u, CS at round 17: G_u is tree 0 part 0 (18 rows over E, 54 symbols), the fresh fold
    // mask tree 0 part 1 (mask symbols after them), the shared split mask tree 2.
    let yu = cs_y(
        17,
        ku,
        shape.test_u[0].h,
        &gamma_u,
        (0, 18),
        2,
        (0, 54),
        (17, 13, 17),
    )?;
    // test_omega, CS at round 32: Omega is tree 1 (4 rows over E), the split mask tree 2, the
    // fresh fold mask tree 5 (sent in round 28).
    let yo = cs_y(
        32,
        ko,
        shape.test_omega[0].h,
        &gamma_o,
        (1, 4),
        2,
        (5, 0),
        (18, 13, 13),
    )?;
    for (base, y) in [(9, yu), (28, yo)] {
        all.push((base, "CS:_y_main_at_the_first_draw", y[0]));
        all.push((base + 1, "CS:_y_0_at_the_first_draw", y[1]));
        all.push((base + 2, "CS:_y_1_at_the_first_draw", y[2]));
    }

    // The whole statement, coefficients included (relation.h): FOLDEQ, SEND, LIN, SPLIT, then
    // per test BAT, FOLD and CS with `switch_rows`; notes 12-15 and 31-34.
    {
        use flashprove_iop::relation::{Statement, VectorLay};
        use flashprove_iop::shapes::{IoppStage, OracleShape};
        use flashprove_iop::{bat, cs, lin, send, split};
        let ext =
            |r: Result<E, flashprove_transcript::TranscriptError>| r.map_err(|e| e.to_string());
        let fold_mask_shape = |s: &IoppStage| OracleShape {
            code: None,
            main_rows: 0,
            main_deg: 1,
            mask_rows: 1 << s.h,
            mask_code: Some(s.mask_code),
            answers: 0,
        };
        let seeds_of =
            |round: u64, shapes: &[OracleShape]| -> Result<Vec<send::SampleSeed>, String> {
                let (bits, answers) = send::seed_shape(&codes, shapes);
                let mut dr = shared.draw(round).ok_or("no seed draw")?;
                let mut out = Vec::new();
                for _ in 0..answers {
                    let z = (0..bits)
                        .map(|_| ext(dr.extension()))
                        .collect::<Result<Vec<E>, String>>()?;
                    let beta = ext(dr.extension_nonzero())?;
                    out.push(send::SampleSeed { z, beta });
                }
                Ok(out)
            };
        let mut st = Statement::new(codes.clone());
        let u_code = shape.fold.u.code.ok_or("G_u has no code")?;
        let o_code = shape.omega.code.ok_or("Omega has no code")?;
        let g_u = st.new_group("LIN: the folded row", u_code, shape.shared_mask_code)?;
        let g_o = st.new_group("LIN: Omega", o_code, shape.shared_mask_code)?;
        // Rounds 2-3: G_u and (masks ahead) test_u's fresh fold mask.
        let u_id = st.sent(shape.fold.u)?;
        let mut sent2 = vec![shape.fold.u];
        let mut ids2 = vec![u_id];
        let mask_u = if shape.masks_ahead {
            let m = fold_mask_shape(&shape.test_u[0]);
            sent2.push(m);
            let id = st.sent(m)?;
            ids2.push(id);
            Some(id)
        } else {
            None
        };
        send::admit_all(&mut st, &ids2, &seeds_of(2, &sent2)?, &u_answers)?;
        st.join(g_u, u_id, false)?;
        let u_lay = VectorLay::of(&codes, &shape.fold.u, shape.fold.rows_high);
        // (Rec_i): record seeds from the chain LABEL_RECORD on the table's name.
        let ix = &shape.fold.index;
        let mut name = root.to_vec();
        name.extend_from_slice(&shared.configuration);
        for v in [
            ix.code.log_n as u64,
            ix.code.ell,
            ix.code.r,
            ix.v as u64,
            ix.answers as u64,
            ix.salt_bytes,
        ] {
            name.extend_from_slice(&v.to_le_bytes());
        }
        const LABEL_RECORD: u64 = 1 << 32;
        let rho0 = flashprove_transcript::first_value(LABEL_RECORD, &[0; 32], &name, None)
            .map_err(|e| e.to_string())?;
        let mut chain =
            flashprove_transcript::Chain::new(LABEL_RECORD, rho0).map_err(|e| e.to_string())?;
        let mut rd = chain
            .close_round(&[], flashprove_transcript::RoundKind::Seed, 0, 0)
            .map_err(|e| e.to_string())?;
        for i in 0..ix.answers {
            let z = (0..ix.code.log_ell())
                .map(|_| ext(rd.extension()))
                .collect::<Result<Vec<E>, String>>()?;
            let beta = ext(rd.extension_nonzero())?;
            let row = foldeq::record_row(
                &shape.fold,
                &send::SampleSeed { z, beta },
                &record,
                i,
                &eq_gamma,
                u_id,
                &u_lay,
            );
            if i == 0 && row.target != n.rec_0_target {
                return Err("(Rec_0): target differs from note 1".into());
            }
            st.add_row(g_u, row)?;
        }
        for &dx in &stored.draw_list {
            let at = stored
                .list
                .binary_search(&dx)
                .map_err(|_| "a draw not in the list")?;
            let y = foldeq::column_symbol(&eq_gamma, &stored.columns[at * rows..(at + 1) * rows]);
            st.add_row(g_u, foldeq::column_row(&shape.fold, dx, y, u_id, &u_lay))?;
        }
        // Rounds 5-6: Omega and the shared split mask.
        let omega_id = st.sent(shape.omega)?;
        let split_id = st.sent(shape.shared_split)?;
        send::admit_all(
            &mut st,
            &[omega_id, split_id],
            &seeds_of(5, &[shape.omega, shape.shared_split])?,
            &omega_split_answers,
        )?;
        st.join(g_o, omega_id, false)?;
        st.join(g_o, split_id, false)?;
        st.join(g_u, split_id, false)?;
        let omega_lay = VectorLay::of(&codes, &shape.omega, shape.omega_rows_high);
        let fold_row = lin::fold_row(&shape, &psi, &zeta, u_id, &u_lay, omega_id, &omega_lay);
        // kappa: the split mask's first free mask entry (MaskLedger::take on a fresh ledger).
        let (first, second) = split::halve(&st, &fold_row, g_o, g_u, split_id, 0, share)?;
        st.add_row(g_o, first)?;
        st.add_row(g_u, second)?;

        // Where each oracle message's symbols are in the opened leaves (TreeBook::sort_out):
        // (tree, offset of its main symbols, offset of its mask symbols), in F symbols. A
        // leaf holds the main symbols of all parts, then the mask symbols of all parts.
        let mut place: BTreeMap<u32, (u32, usize, usize)> = BTreeMap::new();
        place.insert(u_id, (0, 0, 54));
        place.insert(
            mask_u.ok_or("test_u's fold mask is not sent ahead: not ported")?,
            (0, 54, 54),
        );
        place.insert(omega_id, (1, 0, 0));
        place.insert(split_id, (2, 0, 0));
        // The rows of oracle message o at draw k of the opening after round r: (main, mask).
        let rows_at = |st: &Statement,
                       place: &BTreeMap<u32, (u32, usize, usize)>,
                       r: u64,
                       k: usize,
                       o: u32|
         -> Result<(Vec<E>, Vec<E>), String> {
            let &(tree, ms, ks) = place.get(&o).ok_or(format!("oracle {o} has no place"))?;
            let rec = opened(r, tree)?;
            let x = *rec.draw_list.get(k).ok_or("CS: a tree has fewer draws")?;
            let at = rec
                .list
                .binary_search(&x)
                .map_err(|_| "a draw not in its list")?;
            let col = &rec.columns[at * rec.width..(at + 1) * rec.width];
            let sh = &st.oracle(o).shape;
            let read = |from: usize, n: u64, deg: u64| -> Result<Vec<E>, String> {
                let n = n as usize;
                if from + 3 * n > col.len() && deg == 3 {
                    return Err(format!("tree {tree}: the column is too narrow"));
                }
                Ok((0..n)
                    .map(|b| {
                        if deg == 3 {
                            E([
                                col[from + 3 * b],
                                col[from + 3 * b + 1],
                                col[from + 3 * b + 2],
                            ])
                        } else {
                            E::from_base(col[from + b])
                        }
                    })
                    .collect())
            };
            Ok((
                read(ms, sh.main_rows, sh.main_deg)?,
                read(ks, sh.mask_rows, 3)?,
            ))
        };
        // single_rows_symbols at draw k: [main folded, (kept), old mask folded, fresh folded].
        let single_at = |st: &Statement,
                         place: &BTreeMap<u32, (u32, usize, usize)>,
                         r: u64,
                         k: usize,
                         srows: &fold::SingleRows|
         -> Result<Vec<E>, String> {
            let l = &srows.layout;
            let mut main = vec![E::ZERO; 1 << l.k];
            let mut mask = vec![E::ZERO; 1 << l.h];
            for (w, &o) in l.members.iter().enumerate() {
                let (m, z) = rows_at(st, place, r, k, o)?;
                for (b, v) in m.into_iter().enumerate() {
                    main[l.main_first[w] as usize + b] = v;
                }
                for (b, v) in z.into_iter().enumerate() {
                    mask[l.mask_first[w] as usize + b] = v;
                }
            }
            let mut y = vec![fold::fold_low(main, &srows.gamma, l.k)[0]];
            if srows.masks >= 1 {
                y.push(fold::fold_low(mask, &srows.gamma, l.h)[0]);
            }
            if srows.masks == 2 {
                let (_, f) = rows_at(st, place, r, k, srows.fresh)?;
                y.push(fold::fold_low(f, &srows.gamma, l.h)[0]);
            }
            Ok(y)
        };
        struct Test<'a> {
            group: u32,
            stages: &'a [IoppStage],
            bat: u64,
            eps: u64,
            gamma: Vec<E>,
            fold_target: E,
            bat_target: E,
            fresh: u32,
            trees: [u32; 2],
            note: usize,
        }
        // One whole proximity test: BAT, then per stage FOLD and CS, then BASE with its two
        // refusals. Returns the notes, in upstream's order.
        let run_test = |st: &mut Statement,
                        place: &mut BTreeMap<u32, (u32, usize, usize)>,
                        t: Test|
         -> Result<Vec<(usize, &'static str, E)>, String> {
            let input = st.begin_run(t.group)?;
            let mut layout = input.layout.clone();
            let x = ext(shared.draw(t.bat).ok_or("no BAT draw")?.extension())?;
            let mut row = bat::combine(st, t.group, input, x);
            if row.target != t.bat_target {
                return Err(
                    "BAT: the combined claim's target differs from the targets alone".into(),
                );
            }
            let mut notes = Vec::new();
            let mut note = t.note;
            let (mut eps_round, mut gamma, mut fold_t, mut fresh) =
                (t.eps, t.gamma.clone(), t.fold_target, t.fresh);
            let last = t.stages.len() - 1;
            let mut cs_round = 0;
            for i in 0..last {
                let si = t.stages[i];
                layout.k = si.k;
                layout.h = si.h;
                if i > 0 {
                    let (ft, g) = fold_target(eps_round as usize, si.k, row.target)?;
                    fold_t = ft;
                    gamma = g;
                    notes.push((note, "FOLD:_target", ft));
                    note += 1;
                }
                let fs = fold::FoldShape {
                    code: si.code,
                    mask_code: si.mask_code,
                    layout: layout.clone(),
                };
                fold::fold_shape_check(st, &fs)?;
                fold::fold_row_check(st, &fs, &row)?;
                let eps = ext(shared.draw(eps_round).ok_or("no eps draw")?.extension())?;
                let single = fold::fold_output(st, &fs, row, fresh, eps, &gamma, fold_t);
                let seed_round = eps_round + si.k as u64 + 1;
                cs_round = seed_round + 1;
                let next = t.stages[i + 1];
                let to = st.new_group("stage", next.code, next.mask_code)?;
                let target = cs::switch_target_stage(next.code, next.mask_code, next.k, next.h, 1);
                let g = st.sent(target.shape)?;
                let mut shapes = vec![target.shape];
                let mut ids = vec![g];
                if shape.masks_ride {
                    let m = if i + 1 == last {
                        OracleShape {
                            code: Some(next.code),
                            main_rows: 1,
                            main_deg: 3,
                            mask_rows: 1,
                            mask_code: Some(next.mask_code),
                            answers: 0,
                        }
                    } else {
                        fold_mask_shape(&next)
                    };
                    shapes.push(m);
                    ids.push(st.sent(m)?);
                }
                // The new tree: [g | the riding mask], main symbols then mask symbols.
                let tree = t.trees[i];
                let main_w: usize = shapes.iter().map(|s| 3 * s.main_rows as usize).sum();
                let (gm, gk) = (
                    3 * target.shape.main_rows as usize,
                    3 * target.shape.mask_rows as usize,
                );
                place.insert(g, (tree, 0, main_w));
                if ids.len() > 1 {
                    place.insert(ids[1], (tree, gm, main_w + gk));
                }
                let answers = claims::elements(msg(cs_round as usize))?;
                send::admit_all(st, &ids, &seeds_of(seed_round, &shapes)?, &answers)?;
                st.join(to, g, false)?;
                let main_tree = place.get(&single.layout.members[0]).ok_or("no place")?.0;
                let draws = opened(cs_round, main_tree)?.draw_list.clone();
                let ys = (0..draws.len())
                    .map(|k| single_at(st, place, cs_round, k, &single))
                    .collect::<Result<Vec<_>, String>>()?;
                if i == 0 {
                    notes.push((note - 3, "CS:_y_main_at_the_first_draw", ys[0][0]));
                    notes.push((note - 2, "CS:_y_0_at_the_first_draw", ys[0][1]));
                    notes.push((note - 1, "CS:_y_1_at_the_first_draw", ys[0][2]));
                } else {
                    notes.push((note, "CS:_y_main_at_the_first_draw", ys[0][0]));
                    notes.push((note + 1, "CS:_y_0_at_the_first_draw", ys[0][1]));
                    notes.push((note + 2, "CS:_y_1_at_the_first_draw", ys[0][2]));
                    note += 3;
                }
                for r in cs::switch_rows(st, &single, &target, g, &draws, &ys)? {
                    st.add_row(to, r)?;
                }
                let input = st.begin_run(to)?;
                layout = input.layout.clone();
                let theta = ext(shared.draw(cs_round).ok_or("no CS draw")?.extension())?;
                row = bat::combine(st, to, input, theta);
                notes.push((note, "CS:_target", row.target));
                notes.push((note + 1, "CS:_c'[0]", row.c.at(0)));
                notes.push((note + 2, "CS:_d'[0]", *row.d.first().ok_or("CS: no d")?));
                notes.push((
                    note + 3,
                    "CS:_d's_last_entry",
                    *row.d.last().ok_or("CS: no d")?,
                ));
                note += 4;
                eps_round = cs_round + 1;
                fresh = *ids.get(1).ok_or("masks do not ride: not ported")?;
            }
            // BASE (iopp_last_rows, base_verify): the riding base mask is g*.
            let sl = t.stages[last];
            if !(layout.k == 1 && layout.h == 0 && layout.members.len() == 1) {
                return Err(
                    "IOPP: the last stage is one oracle message of one main and one mask row"
                        .into(),
                );
            }
            let mut c = row.c.clone();
            c.fix_low(&[E::ZERO], 1, E::ONE);
            let star = fresh;
            let code = codes.base[sl.code as usize];
            let zk = codes.mask[sl.mask_code as usize];
            let (lam_round, base_round) = (cs_round + 1, cs_round + 2);
            let target_star = match claims::elements(msg(lam_round as usize))?.as_slice() {
                [x] => *x,
                _ => return Err("BASE lambda: one element".into()),
            };
            let lambda = ext(shared.draw(lam_round).ok_or("no lambda")?.extension())?;
            let words = claims::elements(msg(base_round as usize))?;
            let (le, lz) = (code.ell as usize, zk.ell as usize);
            if words.len() != le + lz + code.r as usize + zk.r as usize {
                return Err("BASE: the masked rows have not the codes' lengths".into());
            }
            let m0 = &words[..le];
            let m1 = &words[le..le + lz];
            let r0 = &words[le + lz..le + lz + code.r as usize];
            let r1 = &words[le + lz + code.r as usize..];
            let log_ell = code.log_ell();
            let mut cw = vec![E::ZERO; 1 << log_ell];
            c.add_to(&mut cw, log_ell);
            let left =
                flashprove_iop::ext::inner(&cw[..le], m0) + flashprove_iop::ext::inner(&row.d, m1);
            let right = target_star + lambda * row.target;
            notes.push((note, "BASE:_left_side_of_the_linear_check", left));
            notes.push((note + 1, "BASE:_right_side_of_the_linear_check", right));
            if left != right {
                return Err(
                    "BASE: the masked message in the proof does not satisfy the linear claim"
                        .into(),
                );
            }
            // Refusal 2: the encoding of (M', R') against g* + lambda * (the rows) at each listed position.
            let gid = layout.members[0];
            let base_tree = place.get(&gid).ok_or("no place")?.0;
            place.insert(star, (base_tree, 3, 9));
            place.insert(gid, (base_tree, 0, 6));
            let rec = opened(base_round, base_tree)?;
            let encode = |cj: &flashprove_iop::code::Code, x: u64, m: &[E], r: &[E]| -> E {
                let g = foldeq::GeneratorRow::at(cj, x);
                let mut s = E::ZERO;
                for (j, &v) in m.iter().enumerate() {
                    s += v.scale(g.message(j as u64));
                }
                for (j, &v) in r.iter().enumerate() {
                    s += v.scale(g.tail(j as u64));
                }
                s
            };
            for (k, &x) in rec.draw_list.iter().enumerate() {
                let (gm, gz) = rows_at(st, place, base_round, k, gid)?;
                let (sm, sz) = rows_at(st, place, base_round, k, star)?;
                let xz = x & ((1_u64 << zk.log_n) - 1);
                if encode(&code, x, m0, r0) != sm[0] + lambda * gm[0]
                    || encode(&zk, xz, m1, r1) != sz[0] + lambda * gz[0]
                {
                    return Err("BASE: the encoding of the masked message differs from the opened symbols at a listed position".into());
                }
            }
            Ok(notes)
        };
        let tu = Test {
            group: g_u,
            stages: &shape.test_u,
            bat: 9,
            eps: 10,
            gamma: gamma_u.clone(),
            fold_target: fold_u,
            bat_target: bat_u,
            fresh: mask_u.ok_or("no mask")?,
            trees: [3, 4],
            note: 12,
        };
        let nu = run_test(&mut st, &mut place, tu)?;
        // test_omega's fresh mask comes with FOLD epsilon (round 28), after test_u's messages.
        let mask_o = st.sent(fold_mask_shape(&shape.test_omega[0]))?;
        place.insert(mask_o, (5, 0, 0));
        let to_ = Test {
            group: g_o,
            stages: &shape.test_omega,
            bat: 27,
            eps: 28,
            gamma: gamma_o.clone(),
            fold_target: fold_o,
            bat_target: bat_omega,
            fresh: mask_o,
            trees: [6, 7],
            note: 31,
        };
        let no = run_test(&mut st, &mut place, to_)?;
        st.require_all_tested()?;
        for n in nu.into_iter().chain(no) {
            if !all.iter().any(|a| a.0 == n.0) {
                all.push(n);
            }
        }
        all.sort_by_key(|n| n.0);
        println!(
            "SHARED_CHAIN_ALGEBRA_OK both proximity tests end in BASE with both refusals passed"
        );
    }
    all.sort_by_key(|n| n.0);
    println!(
        "SHARED_CHAIN_CHECK walk=OK table_rows={rows} k_col={} k_lo={} first_draw={x}",
        shape.k_col(),
        shape.k_lo
    );
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
