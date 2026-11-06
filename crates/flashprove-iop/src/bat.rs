//! BAT (`blocks/iop/bat.h`): $\sum_i x^i\,\text{claim}_i$, coefficients and target alike.
//!
//! [`combine`] is `Bat::combine(S, g, in, x)`: the claims of a group (from
//! [`Statement::begin_run`]) as one claim on the whole group. Runs and units of all
//! claims are summed aside (`RowsAside`) and carried once at the end, as upstream does.

use flashprove_field::Ext3 as E;

use crate::relation::{add_to_group_row, GroupId, GroupRow, Row, RowsAside, RunInput, Statement};

/// `Bat::combine(S, g, in, x)`.
pub fn combine(s: &Statement, g: GroupId, input: RunInput, x: E) -> GroupRow {
    let mut out = GroupRow {
        group: g,
        ..GroupRow::default()
    };
    let mut aside = RowsAside::default();
    let mut power = E::ONE;
    for r in input.rows {
        add_to_group_row(s, &input.layout, r, power, &mut out, Some(&mut aside));
        power *= x;
    }
    add_to_group_row(s, &input.layout, aside.sums, E::ONE, &mut out, None);
    out
}

/// `Bat::combine(rows, x, name)`: the same sum for claims that stay on oracle messages.
pub fn combine_rows(rows: &[Row], x: E, name: impl Into<String>) -> Row {
    let mut out = Row::new(name, crate::relation::RowKind::Plain);
    let mut power = E::ONE;
    for r in rows {
        out.add_scaled(r, power);
        power *= x;
    }
    out
}
