//! SPLIT (`blocks/iop/split.h`), verifier side: a plain claim on members of two groups is
//! split into one claim per group. The mask entry $\kappa$ (the first free mask entry of a
//! mask-only oracle message in both groups) enters the first half with $+1$ and the second
//! with $-1$; the prover sends the first half's target $s$, the second's is $t - s$.

use flashprove_field::Ext3 as E;

use crate::relation::{GroupId, OracleId, Part, Row, RowKind, Statement};

/// `Split::halve` and `Split::finish`: the two halves with their targets.
pub fn halve(
    st: &Statement,
    row: &Row,
    g1: GroupId,
    g2: GroupId,
    mask_message: OracleId,
    kappa_index: u64,
    share: E,
) -> Result<(Row, Row), &'static str> {
    if g1 == g2 {
        return Err("split: two different groups");
    }
    if row.kind != RowKind::Plain {
        return Err("split: only a plain row can be split");
    }
    if st.oracle(mask_message).shape.main_rows != 0 {
        return Err("split: the mask entry comes from a message with mask rows only");
    }
    let member = |g: GroupId, o: OracleId| st.group(g).members.contains(&o);
    if !(member(g1, mask_message) && member(g2, mask_message)) {
        return Err("split: the mask message is a member of both groups");
    }
    let mut first = Row::new(format!("{}, first share", row.name), RowKind::Plain);
    let mut second = Row::new(format!("{}, second share", row.name), RowKind::Plain);
    let side = |o: OracleId| -> Result<bool, &'static str> {
        let (a, b) = (member(g1, o), member(g2, o));
        if a == b {
            return Err("split: each oracle message of the row is a member of exactly one group");
        }
        Ok(a)
    };
    for t in &row.terms {
        if side(t.oracle)? {
            &mut first
        } else {
            &mut second
        }
        .terms
        .push(t.clone());
    }
    for u in &row.units {
        if side(u.oracle)? {
            &mut first
        } else {
            &mut second
        }
        .units
        .push(*u);
    }
    for r in &row.runs {
        if side(r.oracle)? {
            &mut first
        } else {
            &mut second
        }
        .runs
        .push(r.clone());
    }
    for f in &row.forms {
        if side(f.oracle)? {
            &mut first
        } else {
            &mut second
        }
        .forms
        .push(f.clone());
    }
    second.add_unit(mask_message, Part::Mask, kappa_index, E::ZERO - E::ONE);
    first.add_unit(mask_message, Part::Mask, kappa_index, E::ONE);
    first.target = share;
    second.target = row.target - share;
    Ok((first, second))
}
