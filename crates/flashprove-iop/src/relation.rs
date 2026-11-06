//! Linear claims on oracle messages and their groups (`blocks/iop/relation.h`).
//!
//! A [`Row`] says $\langle v, m \rangle = t$, where $m$ is the concatenation of the messages
//! that the oracle messages encode and $v$ is a sum of terms ([`Term`]: a [`Tensor`] on one
//! table), units ([`Unit`]: one entry), runs ([`Run`]: written-out coefficients on
//! `first + step * j`) and main forms ([`MainForm`]). The target $t$ is public.
//!
//! A table of an oracle message with $2^a$ rows (a = `row_bits`) and $2^p$ places
//! (p = `place_bits`) has index $b + 2^a c$ for row $b$, place $c$.
//!
//! [`GroupLayout`] places the members' tables in a group's main table ($2^k$ rows) and mask
//! table ($2^h$ rows); [`add_to_group_row`] carries a claim on members to a claim on the group
//! ([`GroupRow`]: coefficients `c` on the main table, `kept` on kept members, `d` on the mask
//! table).
//!
//! A statement fault that a proof can provoke returns `Err` (fail closed); a fault of the
//! program itself (a caller breaking a precondition) panics, as `BLK_REQUIRE` ends the process.

use std::collections::BTreeMap;
use std::sync::Arc;

use flashprove_field::{Ext3 as E, Fp};

use crate::code::{ceil_log2, Codes};
use crate::shapes::OracleShape;
use crate::tensor::{times, Form, Tensor};

pub type OracleId = u32;
pub type GroupId = u32;

/// `Part`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Part {
    Main,
    Mask,
}

/// `Term`: a structured coefficient vector on one table.
#[derive(Debug, Clone)]
pub struct Term {
    pub oracle: OracleId,
    pub part: Part,
    pub v: Tensor,
}
/// `Unit`: a coefficient on one entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Unit {
    pub oracle: OracleId,
    pub part: Part,
    pub index: u64,
    pub coeff: E,
}

#[derive(Debug, Clone)]
enum RunCoeffs {
    Own(Vec<E>),
    /// A stretch of a shared vector over F that no one changes.
    Shared {
        of_many: Arc<Vec<Fp>>,
        from: usize,
        count: usize,
    },
}

/// `Run`: written-out coefficients on entries first, first + step, ... of one table.
#[derive(Debug, Clone)]
pub struct Run {
    pub oracle: OracleId,
    pub part: Part,
    pub first: u64,
    pub step: u64,
    coeffs: RunCoeffs,
}
impl Run {
    pub fn own(oracle: OracleId, part: Part, first: u64, step: u64, own: Vec<E>) -> Self {
        Self {
            oracle,
            part,
            first,
            step,
            coeffs: RunCoeffs::Own(own),
        }
    }
    pub fn shared(
        oracle: OracleId,
        part: Part,
        first: u64,
        step: u64,
        of_many: Arc<Vec<Fp>>,
        from: usize,
        count: usize,
    ) -> Self {
        assert!(
            from <= of_many.len() && count <= of_many.len() - from,
            "run: the stretch does not lie in its vector"
        );
        Self {
            oracle,
            part,
            first,
            step,
            coeffs: RunCoeffs::Shared {
                of_many,
                from,
                count,
            },
        }
    }
    pub fn len(&self) -> usize {
        match &self.coeffs {
            RunCoeffs::Own(v) => v.len(),
            RunCoeffs::Shared { count, .. } => *count,
        }
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    pub fn at(&self, j: usize) -> E {
        match &self.coeffs {
            RunCoeffs::Own(v) => v[j],
            RunCoeffs::Shared { of_many, from, .. } => E::from_base(of_many[from + j]),
        }
    }
    /// `lies_as`: both runs cover the same entries of the same table.
    pub fn lies_as(&self, o: &Run) -> bool {
        self.oracle == o.oracle
            && self.part == o.part
            && self.first == o.first
            && self.step == o.step
            && self.len() == o.len()
    }
    /// `scaled`: x * r, owning its coefficients.
    pub fn scaled(r: &Run, x: E) -> Run {
        let own = (0..r.len()).map(|j| times(x, r.at(j))).collect();
        Run::own(r.oracle, r.part, r.first, r.step, own)
    }
    /// `add_scaled`: this += x * other, entry by entry.
    pub fn add_scaled(&mut self, other: &Run, x: E) {
        assert!(
            self.lies_as(other),
            "run: the two runs lie on different entries"
        );
        let mut own: Vec<E> = (0..self.len()).map(|j| self.at(j)).collect();
        for (j, c) in own.iter_mut().enumerate() {
            *c += times(x, other.at(j));
        }
        self.coeffs = RunCoeffs::Own(own);
    }
}

/// `MainForm`: a whole coefficient vector on the main table of one oracle message.
#[derive(Debug, Clone)]
pub struct MainForm {
    pub oracle: OracleId,
    pub c: Form,
}

/// `RowKind`: a claim's class in BAT's fixed order.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RowKind {
    Plain,
    Sample,
    Generator,
}

/// `Row`: a linear claim.
#[derive(Debug, Clone)]
pub struct Row {
    pub name: String,
    pub kind: RowKind,
    pub terms: Vec<Term>,
    pub units: Vec<Unit>,
    pub runs: Vec<Run>,
    pub forms: Vec<MainForm>,
    pub target: E,
}
impl Row {
    pub fn new(name: impl Into<String>, kind: RowKind) -> Self {
        Self {
            name: name.into(),
            kind,
            terms: Vec::new(),
            units: Vec::new(),
            runs: Vec::new(),
            forms: Vec::new(),
            target: E::ZERO,
        }
    }
    pub fn add(&mut self, oracle: OracleId, part: Part, v: Tensor) {
        self.terms.push(Term { oracle, part, v });
    }
    pub fn add_form(&mut self, oracle: OracleId, c: Form) {
        self.forms.push(MainForm { oracle, c });
    }
    pub fn add_run(&mut self, run: Run) {
        self.runs.push(run);
    }
    pub fn add_unit(&mut self, oracle: OracleId, part: Part, index: u64, coeff: E) {
        self.units.push(Unit {
            oracle,
            part,
            index,
            coeff,
        });
    }
    /// `coefficient`: the claim's total coefficient on one entry.
    pub fn coefficient(&self, o: OracleId, part: Part, index: u64) -> E {
        let mut sum = E::ZERO;
        for t in &self.terms {
            if t.oracle == o && t.part == part {
                sum += t.v.at(index);
            }
        }
        for u in &self.units {
            if u.oracle == o && u.part == part && u.index == index {
                sum += u.coeff;
            }
        }
        for r in &self.runs {
            if r.oracle == o
                && r.part == part
                && index >= r.first
                && (index - r.first) % r.step == 0
                && (index - r.first) / r.step < r.len() as u64
            {
                sum += r.at(((index - r.first) / r.step) as usize);
            }
        }
        for f in &self.forms {
            if f.oracle == o && part == Part::Main {
                sum += f.c.at(index);
            }
        }
        sum
    }
    /// `add_runs_scaled`: this += x * (the runs of other); a run on the same entries as one of
    /// this claim's is added into it.
    pub fn add_runs_scaled(&mut self, other: &Row, x: E) {
        for r in &other.runs {
            match self.runs.iter_mut().find(|m| m.lies_as(r)) {
                Some(same) => same.add_scaled(r, x),
                None => self.runs.push(Run::scaled(r, x)),
            }
        }
    }
    /// `add_scaled`: this += x * other (coefficients and target).
    pub fn add_scaled(&mut self, other: &Row, x: E) {
        for t in &other.terms {
            let mut t = t.clone();
            t.v.scalar *= x;
            self.terms.push(t);
        }
        for u in &other.units {
            self.units.push(Unit {
                coeff: u.coeff * x,
                ..*u
            });
        }
        self.add_runs_scaled(other, x);
        for f in &other.forms {
            let mut f = f.clone();
            f.c.scale(x);
            self.forms.push(f);
        }
        self.target += x * other.target;
    }
}

/// `KeptForm`: a group claim's coefficients on one kept member's own main table.
#[derive(Debug, Clone, Default)]
pub struct KeptForm {
    pub oracle: OracleId,
    pub c: Form,
}
/// `GroupRow`: one claim on a whole group. `c` on the main table ($2^k$ rows), `kept` per kept
/// member in sending order, `d` written out on the mask table ($2^h$ rows).
#[derive(Debug, Clone, Default)]
pub struct GroupRow {
    pub group: GroupId,
    pub c: Form,
    pub kept: Vec<KeptForm>,
    pub d: Vec<E>,
    pub target: E,
}

/// `GroupLayout`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GroupLayout {
    pub k: u32,
    pub h: u32,
    pub log_ell: u32,
    pub log_ell_zk: u32,
    /// In the order of sending.
    pub members: Vec<OracleId>,
    pub kept: Vec<bool>,
    /// First row of each member's block; [`GroupLayout::NONE`] if it has none.
    pub main_first: Vec<u64>,
    pub mask_first: Vec<u64>,
}
impl GroupLayout {
    pub const NONE: u64 = !0;
    /// `find`: the member's place; panics (program fault) if `o` is not a member.
    pub fn find(&self, o: OracleId) -> usize {
        self.members
            .iter()
            .position(|&m| m == o)
            .expect("group: this oracle message is not a member")
    }
}

/// `group_index`: the index, in a group's table with $2^{gb}$ rows, of entry `index` of a
/// member's table with $2^{a}$ rows whose block begins at row `first`.
pub fn group_index(index: u64, row_bits: u32, first: u64, group_row_bits: u32) -> u64 {
    let row = index & ((1_u64 << row_bits) - 1);
    let place = index >> row_bits;
    (first + row) + (place << group_row_bits)
}

/// `VectorLay` (blocks/iop/foldeq.h): how a vector is placed in a main table with
/// $2^{\text{row\_bits}}$ rows of $2^{\text{place\_bits}}$ places.
/// `rows_high = false`: entry j is entry j of the table read as a vector;
/// `rows_high = true`: row $\lfloor j / 2^{p} \rfloor$ holds $2^p$ consecutive entries.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VectorLay {
    pub row_bits: u32,
    pub place_bits: u32,
    pub rows_high: bool,
}
impl VectorLay {
    /// `vector_lay`.
    pub fn of(codes: &Codes, s: &OracleShape, rows_high: bool) -> Self {
        let code = s.code.expect("lay: an oracle shape without main rows");
        Self {
            row_bits: ceil_log2(s.main_rows),
            place_bits: codes.base[code as usize].log_ell(),
            rows_high,
        }
    }
    pub fn bits(&self) -> u32 {
        self.row_bits + self.place_bits
    }
    /// `index`: the table's index of entry j.
    pub fn index(&self, j: u64) -> u64 {
        assert!(j >> self.bits() == 0, "lay: no such entry");
        if self.rows_high {
            (j >> self.place_bits) | ((j & ((1_u64 << self.place_bits) - 1)) << self.row_bits)
        } else {
            j
        }
    }
    /// `entry_at`: the inverse of [`VectorLay::index`].
    pub fn entry_at(&self, index: u64) -> u64 {
        if self.rows_high {
            (index >> self.row_bits) | ((index & ((1_u64 << self.row_bits) - 1)) << self.place_bits)
        } else {
            index
        }
    }
    /// `on_table`: v (indexed by the low `v.vars()` bits of j, 0 above) as a vector on the table.
    pub fn on_table(&self, mut v: Tensor) -> Tensor {
        assert!(
            v.vars() <= self.bits(),
            "lay: the vector is longer than the table"
        );
        let n = v.vars();
        v.insert_choice(n, self.bits() - n, 0);
        if self.rows_high {
            v.rotate(self.place_bits);
            let (p, a) = (self.place_bits, self.row_bits);
            for d in &mut v.dense_vars {
                *d = if *d >= p { *d - p } else { *d + a };
            }
        }
        v
    }
}

/// What a Statement keeps about one oracle message (`Oracle`).
#[derive(Debug, Clone)]
pub struct Oracle {
    pub shape: OracleShape,
    pub sampled: bool,
    pub sample_rows: Vec<Row>,
    pub pad: Vec<(Part, u64)>,
    pub groups: Vec<GroupId>,
}

/// `Group`.
#[derive(Debug, Clone)]
pub struct Group {
    pub name: String,
    pub code: u32,
    pub mask_code: u32,
    pub members: Vec<OracleId>,
    pub kept: Vec<bool>,
    pub rows: Vec<Row>,
    pub in_run: bool,
}

/// `RunInput`: the group's layout and its claims in BAT's order.
#[derive(Debug, Clone)]
pub struct RunInput {
    pub layout: GroupLayout,
    pub rows: Vec<Row>,
}

pub type StatementError = &'static str;

/// `Statement`: verifier side (no engine, no mask ledgers).
#[derive(Debug, Clone)]
pub struct Statement {
    codes: Codes,
    oracles: Vec<Oracle>,
    groups: Vec<Group>,
}
impl Statement {
    pub fn new(codes: Codes) -> Self {
        Self {
            codes,
            oracles: Vec::new(),
            groups: Vec::new(),
        }
    }
    pub fn codes(&self) -> &Codes {
        &self.codes
    }
    pub fn oracle(&self, o: OracleId) -> &Oracle {
        &self.oracles[o as usize]
    }
    pub fn group(&self, g: GroupId) -> &Group {
        &self.groups[g as usize]
    }
    pub fn has(&self, o: OracleId, part: Part) -> bool {
        let s = &self.oracle(o).shape;
        match part {
            Part::Main => s.main_rows > 0,
            Part::Mask => s.mask_rows > 0,
        }
    }
    pub fn row_bits(&self, o: OracleId, part: Part) -> u32 {
        let s = &self.oracle(o).shape;
        ceil_log2(match part {
            Part::Main => s.main_rows,
            Part::Mask => s.mask_rows,
        })
    }
    pub fn place_bits(&self, o: OracleId, part: Part) -> u32 {
        if !self.has(o, part) {
            return 0;
        }
        let s = &self.oracle(o).shape;
        match part {
            Part::Main => {
                self.codes.base[s.code.expect("main rows have a code") as usize].log_ell()
            }
            Part::Mask => {
                self.codes.mask[s.mask_code.expect("mask rows have a code") as usize].log_ell()
            }
        }
    }
    pub fn table_bits(&self, o: OracleId, part: Part) -> u32 {
        self.row_bits(o, part) + self.place_bits(o, part)
    }

    /// `new_group`.
    pub fn new_group(
        &mut self,
        name: impl Into<String>,
        code: u32,
        mask_code: u32,
    ) -> Result<GroupId, StatementError> {
        let (b, m) = (
            self.codes.base.get(code as usize),
            self.codes.mask.get(mask_code as usize),
        );
        let (Some(b), Some(m)) = (b, m) else {
            return Err("statement: no such code");
        };
        if m.log_n > b.log_n {
            return Err("statement: the mask code is longer than the group's");
        }
        self.groups.push(Group {
            name: name.into(),
            code,
            mask_code,
            members: Vec::new(),
            kept: Vec::new(),
            rows: Vec::new(),
            in_run: false,
        });
        Ok((self.groups.len() - 1) as GroupId)
    }
    /// `sent`.
    pub fn sent(&mut self, shape: OracleShape) -> Result<OracleId, StatementError> {
        if shape.main_rows + shape.mask_rows == 0 {
            return Err("statement: an oracle message without rows");
        }
        if shape.main_rows > 0
            && shape
                .code
                .is_none_or(|c| c as usize >= self.codes.base.len())
        {
            return Err("statement: no such base code");
        }
        if shape.mask_rows > 0
            && shape
                .mask_code
                .is_none_or(|c| c as usize >= self.codes.mask.len())
        {
            return Err("statement: no such mask code");
        }
        if shape.main_deg != 1 && shape.main_deg != 3 {
            return Err("statement: main rows are over F or over E");
        }
        self.oracles.push(Oracle {
            shape,
            sampled: false,
            sample_rows: Vec::new(),
            pad: Vec::new(),
            groups: Vec::new(),
        });
        Ok((self.oracles.len() - 1) as OracleId)
    }
    /// What SEND does on sampling (`Statement::sampled`, reached through send.h only): records
    /// the sample claims and the pad. The SEND port (S3) builds both.
    pub fn sampled(
        &mut self,
        o: OracleId,
        sample_rows: Vec<Row>,
        pad: Vec<(Part, u64)>,
    ) -> Result<(), StatementError> {
        let x = self
            .oracles
            .get_mut(o as usize)
            .ok_or("statement: no such oracle message")?;
        if x.sampled {
            return Err("statement: an oracle message is sampled once");
        }
        if sample_rows.iter().any(|r| r.kind != RowKind::Sample) {
            return Err("statement: a sample claim of another kind");
        }
        x.sampled = true;
        x.sample_rows = sample_rows;
        x.pad = pad;
        Ok(())
    }
    /// `join`: o becomes a member of g (members are kept sorted by id, which is sending order).
    pub fn join(&mut self, g: GroupId, o: OracleId, kept: bool) -> Result<(), StatementError> {
        let x = self
            .oracles
            .get(o as usize)
            .ok_or("statement: no such oracle message")?;
        let gr = self
            .groups
            .get(g as usize)
            .ok_or("statement: no such group")?;
        if !x.sampled {
            return Err("statement: only a sampled oracle message can join a group");
        }
        if gr.in_run {
            return Err("statement: the proximity test on this group has begun");
        }
        if x.shape.main_rows != 0 && x.shape.code != Some(gr.code) {
            return Err("statement: a group has one base code");
        }
        if x.shape.mask_rows != 0 && x.shape.mask_code != Some(gr.mask_code) {
            return Err("statement: a group has one mask code");
        }
        if gr.members.contains(&o) {
            return Err("statement: already a member");
        }
        if kept && x.shape.main_rows == 0 {
            return Err("statement: only main rows can be kept");
        }
        let gr = &mut self.groups[g as usize];
        let at = gr.members.partition_point(|&m| m <= o);
        gr.members.insert(at, o);
        gr.kept.insert(at, kept);
        self.oracles[o as usize].groups.push(g);
        Ok(())
    }
    fn check_place(
        &self,
        g: &Group,
        o: OracleId,
        part: Part,
        vars: u32,
        index: u64,
    ) -> Result<(), StatementError> {
        if !g.members.contains(&o) {
            return Err("statement: a row on a group names members of that group only");
        }
        if !self.has(o, part) {
            return Err("statement: a row names a table that the oracle message does not have");
        }
        if vars != self.table_bits(o, part) {
            return Err("statement: a term does not fit its table");
        }
        if index >> self.table_bits(o, part) != 0 {
            return Err("statement: no such entry");
        }
        Ok(())
    }
    /// `add_row`: an open claim on g.
    pub fn add_row(&mut self, g: GroupId, row: Row) -> Result<(), StatementError> {
        let gr = self
            .groups
            .get(g as usize)
            .ok_or("statement: no such group")?;
        if gr.in_run {
            return Err(
                "statement: the rows of a proximity test are fixed before its first challenge",
            );
        }
        if row.kind == RowKind::Sample {
            return Err("statement: sample rows come from SEND alone");
        }
        for t in &row.terms {
            self.check_place(gr, t.oracle, t.part, t.v.vars(), 0)?;
        }
        for u in &row.units {
            self.check_place(
                gr,
                u.oracle,
                u.part,
                self.table_bits(u.oracle, u.part),
                u.index,
            )?;
        }
        for r in &row.runs {
            if r.is_empty() || r.step < 1 {
                return Err("statement: a run of coefficients is empty or has step 0");
            }
            self.check_place(gr, r.oracle, r.part, self.table_bits(r.oracle, r.part), 0)?;
            let entries = 1_u64 << self.table_bits(r.oracle, r.part);
            if r.first >= entries || (r.len() as u64 - 1) > (entries - 1 - r.first) / r.step {
                return Err("statement: no such entry");
            }
        }
        for f in &row.forms {
            self.check_place(
                gr,
                f.oracle,
                Part::Main,
                self.table_bits(f.oracle, Part::Main),
                0,
            )?;
            if !f.c.fits(self.table_bits(f.oracle, Part::Main)) {
                return Err("statement: a part of a coefficient vector does not fit its table");
            }
        }
        for &o in &gr.members {
            for &(p, i) in &self.oracle(o).pad {
                if row.coefficient(o, p, i) != E::ZERO {
                    return Err("statement: a row reads the pad of a sample");
                }
            }
        }
        self.groups[g as usize].rows.push(row);
        Ok(())
    }
    /// `lay`: assigns blocks by decreasing size, ties in sending order; returns rows used.
    fn lay(&self, g: &Group, part: Part, first: &mut Vec<u64>) -> u64 {
        *first = vec![GroupLayout::NONE; g.members.len()];
        let mut order: Vec<usize> = (0..g.members.len())
            .filter(|&i| self.has(g.members[i], part) && !(part == Part::Main && g.kept[i]))
            .collect();
        order.sort_by_key(|&i| std::cmp::Reverse(self.row_bits(g.members[i], part)));
        let mut next = 0;
        for i in order {
            first[i] = next;
            next += 1_u64 << self.row_bits(g.members[i], part);
        }
        next
    }
    /// `layout`.
    pub fn layout(&self, g: GroupId) -> GroupLayout {
        let gr = self.group(g);
        let mut l = GroupLayout {
            k: 0,
            h: 0,
            log_ell: self.codes.base[gr.code as usize].log_ell(),
            log_ell_zk: self.codes.mask[gr.mask_code as usize].log_ell(),
            members: gr.members.clone(),
            kept: gr.kept.clone(),
            main_first: Vec::new(),
            mask_first: Vec::new(),
        };
        let mask_used = self.lay(gr, Part::Mask, &mut l.mask_first);
        let main_used = self.lay(gr, Part::Main, &mut l.main_first);
        l.h = ceil_log2(mask_used);
        l.k = ceil_log2(main_used).max(l.h).max(1);
        l
    }
    /// `begin_run`: PLAIN claims as created, then sample claims member by member, then
    /// GENERATOR claims as created.
    pub fn begin_run(&mut self, g: GroupId) -> Result<RunInput, StatementError> {
        let gr = self
            .groups
            .get(g as usize)
            .ok_or("statement: no such group")?;
        if gr.in_run {
            return Err("statement: one proximity test for each group");
        }
        if gr.members.is_empty() {
            return Err("statement: a group without members");
        }
        let layout = self.layout(g);
        let gr = &mut self.groups[g as usize];
        gr.in_run = true;
        let all = std::mem::take(&mut gr.rows);
        let members = gr.members.clone();
        let (mut rows, mut generators) = (Vec::new(), Vec::new());
        for r in all {
            match r.kind {
                RowKind::Generator => generators.push(r),
                _ => rows.push(r),
            }
        }
        for o in members {
            rows.extend(self.oracles[o as usize].sample_rows.iter().cloned());
        }
        rows.extend(generators);
        Ok(RunInput { layout, rows })
    }
    /// `require_all_tested`.
    pub fn require_all_tested(&self) -> Result<(), StatementError> {
        if self.groups.iter().any(|g| !g.in_run) {
            return Err("statement: the protocol ends with a group that has not been tested");
        }
        if self
            .oracles
            .iter()
            .any(|x| x.sampled && x.groups.is_empty())
        {
            return Err("statement: the protocol ends with an oracle message that is in no group");
        }
        Ok(())
    }
}

/// `RowsAside`: runs summed by the entries they cover and units summed by entry, carried to
/// the group's tables once at the end.
#[derive(Debug, Clone)]
pub struct RowsAside {
    pub sums: Row,
    unit_at: BTreeMap<(OracleId, Part, u64), usize>,
}
impl Default for RowsAside {
    fn default() -> Self {
        Self {
            sums: Row::new("aside", RowKind::Plain),
            unit_at: BTreeMap::new(),
        }
    }
}
impl RowsAside {
    pub fn add_scaled(&mut self, row: &Row, x: E) {
        self.sums.add_runs_scaled(row, x);
        for u in &row.units {
            match self.unit_at.get(&(u.oracle, u.part, u.index)) {
                Some(&at) => self.sums.units[at].coeff += times(x, u.coeff),
                None => {
                    self.unit_at
                        .insert((u.oracle, u.part, u.index), self.sums.units.len());
                    self.sums.units.push(Unit {
                        coeff: times(x, u.coeff),
                        ..*u
                    });
                }
            }
        }
    }
}

/// `add_to_group_row`: acc += x * row, every coefficient vector carried from its member's
/// table to the group's. With `aside`, runs and units go to `aside.sums` instead (to be carried
/// once at the end with x = 1 and no aside).
pub fn add_to_group_row(
    s: &Statement,
    l: &GroupLayout,
    mut row: Row,
    x: E,
    acc: &mut GroupRow,
    aside: Option<&mut RowsAside>,
) {
    if acc.d.is_empty() {
        acc.d = vec![E::ZERO; 1 << (l.h + l.log_ell_zk)];
    }
    let scaled = |c: E| if x == E::ONE { c } else { times(x, c) };
    fn kept_form(acc: &mut GroupRow, o: OracleId) -> &mut KeptForm {
        let at = acc.kept.partition_point(|k| k.oracle < o);
        if at == acc.kept.len() || acc.kept[at].oracle != o {
            acc.kept.insert(
                at,
                KeptForm {
                    oracle: o,
                    c: Form::default(),
                },
            );
        }
        &mut acc.kept[at]
    }
    for t in std::mem::take(&mut row.terms) {
        let i = l.find(t.oracle);
        let mut v = t.v;
        v.scalar *= x;
        if t.part == Part::Main && l.kept[i] {
            kept_form(acc, t.oracle).c.add(v);
            continue;
        }
        let a = s.row_bits(t.oracle, t.part);
        let (first, bits) = match t.part {
            Part::Main => (l.main_first[i], l.k),
            Part::Mask => (l.mask_first[i], l.h),
        };
        v.insert_choice(a, bits - a, first >> a); // the bits above the block pick the block
        match t.part {
            Part::Main => acc.c.add(v),
            Part::Mask => v.add_to(&mut acc.d),
        }
    }
    let carry_entry =
        |acc: &mut GroupRow, i: usize, o: OracleId, part: Part, a: u32, index: u64, coeff: E| {
            if part == Part::Mask {
                acc.d[group_index(index, a, l.mask_first[i], l.h) as usize] += scaled(coeff);
            } else if l.kept[i] {
                kept_form(acc, o).c.add_entry(index, scaled(coeff));
            } else {
                acc.c
                    .add_entry(group_index(index, a, l.main_first[i], l.k), scaled(coeff));
            }
        };
    if let Some(aside) = aside {
        aside.add_scaled(&row, x);
    } else {
        for u in &row.units {
            let a = s.row_bits(u.oracle, u.part);
            carry_entry(acc, l.find(u.oracle), u.oracle, u.part, a, u.index, u.coeff);
        }
        for r in &row.runs {
            let i = l.find(r.oracle);
            let a = s.row_bits(r.oracle, r.part);
            for j in 0..r.len() {
                carry_entry(
                    acc,
                    i,
                    r.oracle,
                    r.part,
                    a,
                    r.first + r.step * j as u64,
                    r.at(j),
                );
            }
        }
    }
    for f in std::mem::take(&mut row.forms) {
        let i = l.find(f.oracle);
        if l.kept[i] {
            kept_form(acc, f.oracle).c.add_form(f.c, x);
            continue;
        }
        let a = s.row_bits(f.oracle, Part::Main);
        let mut c = f.c;
        c.insert_choice(a, l.k - a, l.main_first[i] >> a);
        acc.c.add_form(c, x);
    }
    acc.target += x * row.target;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::code::Code;

    fn e(a: u64, b: u64, c: u64) -> E {
        E([
            Fp::from_canonical(a).unwrap(),
            Fp::from_canonical(b).unwrap(),
            Fp::from_canonical(c).unwrap(),
        ])
    }
    fn codes() -> Codes {
        Codes {
            base: vec![Code {
                log_n: 6,
                ell: 8,
                r: 2,
            }],
            mask: vec![Code {
                log_n: 4,
                ell: 2,
                r: 1,
            }],
        }
    }
    fn shape(main_rows: u64, mask_rows: u64) -> OracleShape {
        OracleShape {
            code: (main_rows > 0).then_some(0),
            main_rows,
            main_deg: 3,
            mask_rows,
            mask_code: (mask_rows > 0).then_some(0),
            answers: 1,
        }
    }
    /// Three members: A (3 main rows, 1 mask row), B (5 main rows, kept), C (2 main, 2 mask).
    fn statement() -> (Statement, GroupId, [OracleId; 3]) {
        let mut s = Statement::new(codes());
        let g = s.new_group("g", 0, 0).unwrap();
        let ids = [
            s.sent(shape(3, 1)).unwrap(),
            s.sent(shape(5, 0)).unwrap(),
            s.sent(shape(2, 2)).unwrap(),
        ];
        for (n, &o) in ids.iter().enumerate() {
            s.sampled(o, Vec::new(), Vec::new()).unwrap();
            s.join(g, o, n == 1).unwrap();
        }
        (s, g, ids)
    }

    #[test]
    fn layout_places_blocks_by_size_then_order() {
        let (s, g, _) = statement();
        let l = s.layout(g);
        // Main: A takes 4 rows, C 2; B is kept. Mask: C 2 rows, A 1.
        assert_eq!(l.main_first, vec![0, GroupLayout::NONE, 4]);
        assert_eq!(l.mask_first, vec![2, GroupLayout::NONE, 0]);
        assert_eq!((l.k, l.h, l.log_ell, l.log_ell_zk), (3, 2, 3, 1));
    }

    #[test]
    fn group_row_has_each_members_coefficients_at_group_index() {
        let (s, g, [a, b, c]) = statement();
        let l = s.layout(g);
        let mut row = Row::new("r", RowKind::Plain);
        let za: Vec<E> = (0..s.table_bits(a, Part::Main))
            .map(|i| e(i as u64 + 2, 1, 0))
            .collect();
        row.add(a, Part::Main, Tensor::eq(&za, e(3, 0, 0)));
        let zm: Vec<E> = (0..s.table_bits(c, Part::Mask))
            .map(|i| e(5, i as u64, 1))
            .collect();
        row.add(c, Part::Mask, Tensor::eq(&zm, E::ONE));
        row.add_unit(c, Part::Main, 9, e(7, 0, 0));
        row.add_unit(a, Part::Mask, 1, e(1, 1, 1));
        row.add_run(Run::own(b, Part::Main, 2, 8, vec![e(4, 0, 0), e(0, 4, 0)]));
        row.add_run(Run::shared(
            c,
            Part::Main,
            1,
            2,
            Arc::new(vec![Fp::from_canonical(11).unwrap(); 5]),
            1,
            3,
        ));
        let mut fb = Form::default();
        fb.add_entry(17, e(2, 2, 0));
        row.add_form(b, fb);
        let mut fa = Form::default();
        fa.add(Tensor::eq(&za, e(0, 0, 1)));
        row.add_form(a, fa);
        row.target = e(1, 2, 3);
        let x = e(6, 1, 2);

        let mut direct = GroupRow::default();
        add_to_group_row(&s, &l, row.clone(), x, &mut direct, None);
        let mut via = GroupRow::default();
        let mut aside = RowsAside::default();
        add_to_group_row(&s, &l, row.clone(), x, &mut via, Some(&mut aside));
        add_to_group_row(&s, &l, aside.sums, E::ONE, &mut via, None);

        for acc in [&direct, &via] {
            assert_eq!(acc.target, x * row.target);
            let main_bits = l.k + l.log_ell;
            let mask_bits = l.h + l.log_ell_zk;
            for j in 0..1_u64 << main_bits {
                let mut want = E::ZERO;
                for (i, &o) in l.members.iter().enumerate() {
                    if l.kept[i] {
                        continue;
                    }
                    let ra = s.row_bits(o, Part::Main);
                    for idx in 0..1_u64 << s.table_bits(o, Part::Main) {
                        if group_index(idx, ra, l.main_first[i], l.k) == j {
                            want += x * row.coefficient(o, Part::Main, idx);
                        }
                    }
                }
                assert_eq!(acc.c.at(j), want, "main entry {j}");
            }
            for j in 0..1_u64 << mask_bits {
                let mut want = E::ZERO;
                for (i, &o) in l.members.iter().enumerate() {
                    if !s.has(o, Part::Mask) {
                        continue;
                    }
                    let ra = s.row_bits(o, Part::Mask);
                    for idx in 0..1_u64 << s.table_bits(o, Part::Mask) {
                        if group_index(idx, ra, l.mask_first[i], l.h) == j {
                            want += x * row.coefficient(o, Part::Mask, idx);
                        }
                    }
                }
                assert_eq!(acc.d[j as usize], want, "mask entry {j}");
            }
            assert_eq!(acc.kept.len(), 1);
            assert_eq!(acc.kept[0].oracle, b);
            for idx in 0..1_u64 << s.table_bits(b, Part::Main) {
                assert_eq!(
                    acc.kept[0].c.at(idx),
                    x * row.coefficient(b, Part::Main, idx)
                );
            }
        }
    }

    #[test]
    fn statement_faults_fail_closed_and_begin_run_orders_claims() {
        let (mut s, g, [a, _, c]) = statement();
        let mut bad = Row::new("bad", RowKind::Plain);
        bad.add_unit(a, Part::Main, 1 << 5, E::ONE);
        assert_eq!(s.add_row(g, bad), Err("statement: no such entry"));
        let mut short = Row::new("short", RowKind::Plain);
        short.add(a, Part::Main, Tensor::eq(&[E::ONE], E::ONE));
        assert_eq!(
            s.add_row(g, short),
            Err("statement: a term does not fit its table")
        );
        assert!(s.add_row(g, Row::new("s", RowKind::Sample)).is_err());
        s.add_row(g, Row::new("gen", RowKind::Generator)).unwrap();
        let mut p = Row::new("plain", RowKind::Plain);
        p.add_unit(c, Part::Mask, 3, E::ONE);
        s.add_row(g, p).unwrap();
        let run = s.begin_run(g).unwrap();
        let names: Vec<&str> = run.rows.iter().map(|r| r.name.as_str()).collect();
        assert_eq!(names, ["plain", "gen"]);
        assert!(s.add_row(g, Row::new("late", RowKind::Plain)).is_err());
        assert!(s.begin_run(g).is_err());
        s.require_all_tested().unwrap();
    }

    #[test]
    fn vector_lay_on_table_follows_index() {
        let codes = codes();
        for rows_high in [false, true] {
            let lay = VectorLay::of(&codes, &shape(4, 0), rows_high);
            assert_eq!(lay.bits(), 5);
            let mut v = Tensor::eq(&[e(3, 1, 4), e(1, 5, 9)], e(2, 0, 0));
            v.push_dense(1);
            v.set_values(Arc::new(vec![e(5, 0, 0), e(0, 7, 0)]), 0);
            let t = lay.on_table(v.clone());
            for j in 0..32_u64 {
                let want = if j < 8 { v.at(j) } else { E::ZERO };
                assert_eq!(t.at(lay.index(j)), want, "rows_high {rows_high}, j {j}");
                assert_eq!(lay.entry_at(lay.index(j)), j);
            }
        }
    }
}
