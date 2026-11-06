//! The shared chain (`FRM\x03`) verified algebraically, block by block (stages D7 + D9).
//!
//! [`shared_chain_notes`] runs, on the native walk's draws and openings: FOLDEQ, SEND,
//! LIN (Fold), SPLIT, then for test_u and test_omega BAT, FOLD and CS per stage and BASE
//! with its two refusals (the linear check and the encoding check at every listed
//! position). It returns upstream's 45 block notes (`VerifierContext::notes`) in order;
//! an `Err` is a rejection.
use crate::{parse_items, ProofWalk, LABEL_PROOF_SHARED_CHAIN};
use flashprove_field::{Ext3 as E, Fp};
use flashprove_iop::claims;
use flashprove_iop::code::Codes;
use flashprove_iop::fold;
use flashprove_iop::foldeq;
use flashprove_iop::shapes::LinShape;
use flashprove_transcript::first_query::parse_parameters;

/// One note: upstream's index, its name (spaces as `_`), its value.
pub type Note = (usize, &'static str, E);

/// The shared chain's notes; `Err` if a check rejects or the proof does not have the
/// expected shape. `shared_parameters`, `shared_statement`: the shared chain's first query.
pub fn shared_chain_notes(
    proof: &[u8],
    w: &ProofWalk,
    shared_parameters: &[u8],
    shared_statement: &[u8],
) -> Result<Vec<Note>, String> {
    let shared = w
        .chains
        .iter()
        .find(|c| c.label == LABEL_PROOF_SHARED_CHAIN)
        .ok_or("no shared chain")?;

    // The bound shapes, parsed canonically from the shared chain's own first query.
    let p3 = parse_parameters(shared_parameters).map_err(|e| e.to_string())?;
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
    let s3 = parse_items(shared_statement).map_err(|e| e.to_string())?;
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
    // The opening of `tree` that follows round `after`.
    let opened = |after: u64, tree: u32| {
        shared
            .openings
            .iter()
            .find(|o| o.after_round == after && o.tree == tree)
            .ok_or(format!("no opening of tree {tree} after round {after}"))
    };
    // The whole statement, coefficients included (relation.h): FOLDEQ, SEND, LIN, SPLIT, then
    // per test BAT, FOLD and CS with `switch_rows`; notes 12-15 and 31-34.
    {
        use flashprove_iop::book::{OracleNotice, TreeBook};
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
        let mut book = TreeBook::new(0);
        let notice = |shape: OracleShape, leaf_class: u32| OracleNotice { shape, leaf_class };
        let mut sent2 = vec![notice(shape.fold.u, shape.fold.leaf_class)];
        if shape.masks_ahead {
            sent2.push(notice(
                fold_mask_shape(&shape.test_u[0]),
                shape.fold.leaf_class,
            ));
        }
        let ids2 = book.enter(&mut st, &sent2)?;
        let sent2: Vec<OracleShape> = sent2.iter().map(|n| n.shape).collect();
        let u_id = ids2[0];
        let mask_u = ids2.get(1).copied();
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
        let ids5 = book.enter(
            &mut st,
            &[
                notice(shape.omega, shape.omega_leaf_class),
                notice(shape.shared_split, shape.shared_split_leaf_class),
            ],
        )?;
        let (omega_id, split_id) = (ids5[0], ids5[1]);
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

        // The rows of oracle message o at draw k of the opening after round r: (main, mask).
        let rows_at = |st: &Statement,
                       book: &TreeBook,
                       r: u64,
                       k: usize,
                       o: u32|
         -> Result<(Vec<E>, Vec<E>), String> {
            let p = book.place(o).ok_or(format!("oracle {o} has no place"))?;
            let (tree, ms, ks) = (p.tree, p.main_at as usize, p.mask_at as usize);
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
                         book: &TreeBook,
                         r: u64,
                         k: usize,
                         srows: &fold::SingleRows|
         -> Result<Vec<E>, String> {
            let l = &srows.layout;
            let mut main = vec![E::ZERO; 1 << l.k];
            let mut mask = vec![E::ZERO; 1 << l.h];
            for (w, &o) in l.members.iter().enumerate() {
                let (m, z) = rows_at(st, book, r, k, o)?;
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
                let (_, f) = rows_at(st, book, r, k, srows.fresh)?;
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
            note: usize,
        }
        // One whole proximity test: BAT, then per stage FOLD and CS, then BASE with its two
        // refusals. Returns the notes, in upstream's order.
        let run_test = |st: &mut Statement,
                        book: &mut TreeBook,
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
                let mut shapes = vec![target.shape];
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
                }
                let notices: Vec<OracleNotice> = shapes.iter().map(|&s| notice(s, 0)).collect();
                let ids = book.enter(st, &notices)?;
                let g = ids[0];
                let answers = claims::elements(msg(cs_round as usize))?;
                send::admit_all(st, &ids, &seeds_of(seed_round, &shapes)?, &answers)?;
                st.join(to, g, false)?;
                let main_tree = book.place(single.layout.members[0]).ok_or("no place")?.tree;
                let draws = opened(cs_round, main_tree)?.draw_list.clone();
                let ys = (0..draws.len())
                    .map(|k| single_at(st, book, cs_round, k, &single))
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
            let base_tree = book.place(gid).ok_or("no place")?.tree;
            if book.place(star).map(|p| p.tree) != Some(base_tree) {
                return Err("BASE: g* is not in the last stage's tree".into());
            }
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
                let (gm, gz) = rows_at(st, book, base_round, k, gid)?;
                let (sm, sz) = rows_at(st, book, base_round, k, star)?;
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
            note: 12,
        };
        let nu = run_test(&mut st, &mut book, tu)?;
        // test_omega's fresh mask comes with FOLD epsilon (round 28), after test_u's messages.
        let mask_o = book.enter(&mut st, &[notice(fold_mask_shape(&shape.test_omega[0]), 0)])?[0];
        let to_ = Test {
            group: g_o,
            stages: &shape.test_omega,
            bat: 27,
            eps: 28,
            gamma: gamma_o.clone(),
            fold_target: fold_o,
            bat_target: bat_omega,
            fresh: mask_o,
            note: 31,
        };
        let no = run_test(&mut st, &mut book, to_)?;
        st.require_all_tested()?;
        for n in nu.into_iter().chain(no) {
            if !all.iter().any(|a| a.0 == n.0) {
                all.push(n);
            }
        }
        all.sort_by_key(|n| n.0);
    }
    all.sort_by_key(|n| n.0);
    Ok(all)
}
