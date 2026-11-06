//! CS, the code switch (`blocks/iop/cs.h`), verifier side, for groups without kept members.
//!
//! The new oracle message $g$ stores the old main row's message (block `main` of its main
//! table) and "the rest" (block `rest`): the mask rows' messages, the main row's random tail,
//! the mask rows' random tails, in that order, skipping $g$'s own pad. Each old row's symbol
//! at a drawn position $x$ becomes a GENERATOR claim on $g$: the old code's generator row at
//! $x$ (for a mask row, the mask code's at $x \bmod 2^{\log n_{zk}}$). The old claim is carried
//! over as one PLAIN claim on $g$.

use std::sync::Arc;

use flashprove_field::{Ext3 as E, Fp};

use crate::code::{ceil_log2, Code, Codes};
use crate::fold::SingleRows;
use crate::foldeq::GeneratorRow;
use crate::relation::{OracleId, Part, Row, RowKind, Run, Statement};
use crate::send;
use crate::shapes::{OracleShape, E_DEGREE};
use crate::tensor::{Form, Tensor};

/// `Cut`: an aligned block of $2^{\text{bits}}$ rows of one table; entry j sits in row
/// `first_row + j mod 2^bits`, at place `j >> bits`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Cut {
    pub part: Part,
    pub bits: u32,
    pub first_row: u64,
}

/// `SwitchTarget` (no kept members).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SwitchTarget {
    pub shape: OracleShape,
    pub main: Cut,
    pub rest: Cut,
}

/// `switch_target_stage`.
pub fn switch_target_stage(
    code: u32,
    mask_code: u32,
    k: u32,
    h: u32,
    answers: u32,
) -> SwitchTarget {
    SwitchTarget {
        shape: OracleShape {
            code: Some(code),
            main_rows: 1 << k,
            main_deg: E_DEGREE,
            mask_rows: 1 << h,
            mask_code: Some(mask_code),
            answers,
        },
        main: Cut {
            part: Part::Main,
            bits: k,
            first_row: 0,
        },
        rest: Cut {
            part: Part::Mask,
            bits: h,
            first_row: 0,
        },
    }
}

fn row_bits(t: &SwitchTarget, part: Part) -> u32 {
    ceil_log2(match part {
        Part::Main => t.shape.main_rows,
        Part::Mask => t.shape.mask_rows,
    })
}
fn row_length(codes: &Codes, t: &SwitchTarget, part: Part) -> u64 {
    match part {
        Part::Main => codes.base[t.shape.code.expect("code") as usize].ell,
        Part::Mask => codes.mask[t.shape.mask_code.expect("mask code") as usize].ell,
    }
}
/// `cut_index`.
pub fn cut_index(cut: &Cut, table_row_bits: u32, j: u64) -> u64 {
    (cut.first_row + (j & ((1_u64 << cut.bits) - 1))) + ((j >> cut.bits) << table_row_bits)
}

/// `SwitchParts` without kept rows: offsets in the rest.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SwitchParts {
    pub mask_at: Vec<u64>,
    pub main_tail_at: u64,
    pub mask_tail_at: Vec<u64>,
    pub length: u64,
}
pub fn switch_parts(codes: &Codes, input: &SingleRows) -> SwitchParts {
    let zk = codes.mask[input.mask_code as usize];
    let base = codes.base[input.code as usize];
    let mut len = 0;
    let mut mask_at = Vec::new();
    for _ in 0..input.masks {
        mask_at.push(len);
        len += zk.ell;
    }
    let main_tail_at = len;
    len += base.r;
    let mut mask_tail_at = Vec::new();
    for _ in 0..input.masks {
        mask_tail_at.push(len);
        len += zk.r;
    }
    SwitchParts {
        mask_at,
        main_tail_at,
        mask_tail_at,
        length: len,
    }
}

/// `SwitchPlaces`: the rest's entries in fill order, skipping $g$'s pad.
#[derive(Debug, Clone)]
pub struct SwitchPlaces {
    cut: Cut,
    row_bits: u32,
    pad: Vec<u64>,
    size: u64,
}
impl SwitchPlaces {
    pub fn new(codes: &Codes, t: &SwitchTarget) -> Result<Self, &'static str> {
        let cut = t.rest;
        let rb = row_bits(t, cut.part);
        let room = row_length(codes, t, cut.part) << cut.bits;
        let mut pad = Vec::new();
        for p in send::pad(codes, &t.shape)? {
            let row = p.index & ((1_u64 << rb) - 1);
            let place = p.index >> rb;
            if p.part == cut.part && row >= cut.first_row && row < cut.first_row + (1 << cut.bits) {
                pad.push((row - cut.first_row) + (place << cut.bits));
            }
        }
        pad.sort_unstable();
        Ok(Self {
            cut,
            row_bits: rb,
            size: room - pad.len() as u64,
            pad,
        })
    }
    pub fn len(&self) -> u64 {
        self.size
    }
    pub fn is_empty(&self) -> bool {
        self.size == 0
    }
    pub fn at(&self, i: u64) -> u64 {
        let mut j = i;
        for &p in &self.pad {
            if p <= j {
                j += 1;
            }
        }
        cut_index(&self.cut, self.row_bits, j)
    }
}

/// `switch_lift`.
pub fn switch_lift(
    mut c: Form,
    vars: u32,
    cut: &Cut,
    table_row_bits: u32,
    table_bits: u32,
) -> Form {
    assert!(vars >= cut.bits, "CS: the vector is shorter than its block");
    let above = table_row_bits - cut.bits;
    c.insert_choice(cut.bits, above, cut.first_row >> cut.bits);
    c.insert_choice(vars + above, table_bits - (vars + above), 0);
    c
}

/// `SwitchPiece`.
#[derive(Debug, Clone, Copy)]
struct Piece {
    from: usize,
    to: usize,
    first: u64,
    step: u64,
}
fn pieces(places: &SwitchPlaces, first: u64, count: u64) -> Vec<Piece> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < count {
        let begin = places.at(first + i);
        let step = if i + 1 < count {
            places.at(first + i + 1) - begin
        } else {
            1
        };
        let mut end = i + 1;
        let mut last = begin;
        while end < count && places.at(first + end) == last + step {
            last += step;
            end += 1;
        }
        out.push(Piece {
            from: i as usize,
            to: end as usize,
            first: begin,
            step,
        });
        i = end;
    }
    out
}
fn add_rest_own(row: &mut Row, g: OracleId, part: Part, ps: &[Piece], coeff: &[E]) {
    assert_eq!(
        coeff.len(),
        ps.last().map_or(0, |p| p.to),
        "CS: one coefficient per entry"
    );
    for p in ps {
        row.add_run(Run::own(
            g,
            part,
            p.first,
            p.step,
            coeff[p.from..p.to].to_vec(),
        ));
    }
}
fn add_rest_shared(row: &mut Row, g: OracleId, part: Part, ps: &[Piece], coeff: &Arc<Vec<Fp>>) {
    assert_eq!(
        coeff.len(),
        ps.last().map_or(0, |p| p.to),
        "CS: one coefficient per entry"
    );
    for p in ps {
        row.add_run(Run::shared(
            g,
            part,
            p.first,
            p.step,
            coeff.clone(),
            p.from,
            p.to - p.from,
        ));
    }
}

/// `SwitchBox`.
#[derive(Debug, Clone, Copy, Default)]
struct SwitchBox {
    is: bool,
    shift: u32,
    start: u64,
}
fn switch_box(places: &SwitchPlaces, first: u64, vars: u32) -> SwitchBox {
    let mut b = SwitchBox::default();
    let count = 1_u64 << vars;
    if vars == 0 || first + count > places.len() {
        return b;
    }
    let step = places.at(first + 1) - places.at(first);
    if step == 0 || step & (step - 1) != 0 {
        return b;
    }
    for i in 1..count {
        if places.at(first + i) != places.at(first) + i * step {
            return b;
        }
    }
    b.shift = ceil_log2(step);
    b.start = places.at(first);
    b.is = ((b.start >> b.shift) & (count - 1)) == 0;
    b
}
fn switch_on_box(b: &SwitchBox, mut v: Tensor, vars: u32, table_bits: u32) -> Tensor {
    v.insert_choice(0, b.shift, b.start & ((1_u64 << b.shift) - 1));
    v.insert_choice(
        b.shift + vars,
        table_bits - b.shift - vars,
        b.start >> (b.shift + vars),
    );
    v
}

fn generator_tables(code: &Code, x: u64, message: bool) -> (Vec<Fp>, Vec<Fp>) {
    let g = GeneratorRow::at(code, x);
    let m = if message {
        (0..code.ell).map(|j| g.message(j)).collect()
    } else {
        Vec::new()
    };
    let t = (0..code.r).map(|j| g.tail(j)).collect();
    (m, t)
}

/// `switch_rows` for an old group without kept members. `draws`: the positions in the
/// order drawn; `ys[k]`: the single rows' symbols at `draws[k]`
/// ([main, old mask, fresh mask]).
pub fn switch_rows(
    st: &Statement,
    input: &SingleRows,
    t: &SwitchTarget,
    g: OracleId,
    draws: &[u64],
    ys: &[Vec<E>],
) -> Result<Vec<Row>, &'static str> {
    let codes = st.codes();
    if !input.kept.is_empty() || input.kept_rows != 0 {
        return Err("CS: kept members are not ported");
    }
    if input.masks != 2 {
        return Err("CS: the single rows are not those that a fold leaves");
    }
    if ys.len() != draws.len() || ys.iter().any(|y| y.len() != 3) {
        return Err("CS: one symbol for each row at each draw");
    }
    let parts = switch_parts(codes, input);
    let places = SwitchPlaces::new(codes, t)?;
    if parts.length > places.len() {
        return Err("CS: the rest does not fit its block");
    }
    let rb = row_bits(t, Part::Main);
    let table_bits = rb + codes.base[t.shape.code.expect("code") as usize].log_ell();
    let code = codes.base[input.code as usize];
    let zk = codes.mask[input.mask_code as usize];
    let zk_is_a_cube = zk.ell & (zk.ell - 1) == 0;
    let rest_bits = st.table_bits(g, t.rest.part);
    let boxes: Vec<SwitchBox> = (0..input.masks as usize)
        .map(|j| {
            if zk_is_a_cube {
                switch_box(&places, parts.mask_at[j], ceil_log2(zk.ell))
            } else {
                SwitchBox::default()
            }
        })
        .collect();
    let main_tail = pieces(&places, parts.main_tail_at, code.r);
    let mask_message: Vec<Vec<Piece>> = (0..input.masks as usize)
        .map(|j| {
            if boxes[j].is {
                Vec::new()
            } else {
                pieces(&places, parts.mask_at[j], zk.ell)
            }
        })
        .collect();
    let mask_tail: Vec<Vec<Piece>> = (0..input.masks as usize)
        .map(|j| pieces(&places, parts.mask_tail_at[j], zk.r))
        .collect();
    let mut rows = Vec::new();
    {
        let mut old = Row::new("claim carried through a code switch", RowKind::Plain);
        old.add_form(
            g,
            switch_lift(input.c.clone(), code.log_ell(), &t.main, rb, table_bits),
        );
        for j in 0..input.masks as usize {
            let ps = pieces(&places, parts.mask_at[j], input.d[j].len() as u64);
            add_rest_own(&mut old, g, t.rest.part, &ps, &input.d[j]);
        }
        old.target = input.target;
        rows.push(old);
    }
    for (k, &x) in draws.iter().enumerate() {
        let symbols = &ys[k];
        let at_x = GeneratorRow::at(&code, x);
        let mut on_message = Form::default();
        on_message.add(Tensor::product(
            &at_x.f[..code.log_ell() as usize],
            E::from_base(at_x.message_scale),
        ));
        let (_, tail) = generator_tables(&code, x, false);
        let on_tail = Arc::new(tail);
        {
            let mut gen = Row::new("generator row", RowKind::Generator);
            gen.add_form(
                g,
                switch_lift(on_message, code.log_ell(), &t.main, rb, table_bits),
            );
            add_rest_shared(&mut gen, g, t.rest.part, &main_tail, &on_tail);
            gen.target = symbols[0];
            rows.push(gen);
        }
        for j in 0..input.masks as usize {
            let x_zk = x & ((1_u64 << zk.log_n) - 1); // mask_position
            let (zm, zt) = generator_tables(&zk, x_zk, !boxes[j].is);
            let mut gen = Row::new("generator row", RowKind::Generator);
            if boxes[j].is {
                let at_zk = GeneratorRow::at(&zk, x_zk);
                let v = Tensor::product(
                    &at_zk.f[..ceil_log2(zk.ell) as usize],
                    E::from_base(at_zk.message_scale),
                );
                gen.add(
                    g,
                    t.rest.part,
                    switch_on_box(&boxes[j], v, ceil_log2(zk.ell), rest_bits),
                );
            } else {
                add_rest_shared(&mut gen, g, t.rest.part, &mask_message[j], &Arc::new(zm));
            }
            add_rest_shared(&mut gen, g, t.rest.part, &mask_tail[j], &Arc::new(zt));
            gen.target = symbols[1 + j];
            rows.push(gen);
        }
    }
    Ok(rows)
}
