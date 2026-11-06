//! LIN's shared part (`blocks/iop/lin.h`): the claim (Fold) ties Omega to the folded row G_u.
//!
//! With $\psi \in E^{k_{col}}$ (round LIN point) and $\zeta \in E^{k_{row}}$ (round LIN zeta),
//! `lin_fold_row` is the linear form with
//! $$c_\Omega(j) = \mathrm{eq}(j, \zeta)\ \ (j < \text{matrix\_rows}),\qquad
//!   c_{G_u}(j) = -\,\mathrm{eq}(j_{lo}, \psi_{<k_{lo}})\cdot \mathrm{eq}(j_{hi}, \zeta)\ \ (j_{hi} < \text{matrix\_rows}),$$
//! where $j_{lo}$ are the low $k_{lo}$ bits of $j$ and $j_{hi} = j \gg k_{lo}$, and target 0:
//! $\langle c_\Omega, \Omega\rangle + \langle c_{G_u}, G_u\rangle = 0$.
//! Coefficients are by vector index; `VectorLay::index` places them on the table.

use crate::ext::eq_index;
use crate::shapes::LinShape;
use flashprove_field::Ext3 as E;

/// $c_\Omega(j)$.
pub fn fold_on_omega(s: &LinShape, zeta: &[E], j: u64) -> E {
    if j >= s.matrix_rows {
        return E::ZERO;
    }
    eq_index(j, zeta, s.k_row())
}
/// $c_{G_u}(j)$.
pub fn fold_on_u(s: &LinShape, psi: &[E], zeta: &[E], j: u64) -> E {
    let hi = j >> s.k_lo;
    if hi >= s.matrix_rows || (hi >> s.k_row()) != 0 {
        return E::ZERO;
    }
    E::ZERO - eq_index(j, psi, s.k_lo) * eq_index(hi, zeta, s.k_row())
}

/// `lin_fold_row`: the claim (Fold) as a [`Row`](crate::relation::Row) on Omega and G_u
/// (target 0).
pub fn fold_row(
    s: &LinShape,
    psi: &[E],
    zeta: &[E],
    u: crate::relation::OracleId,
    u_lay: &crate::relation::VectorLay,
    omega: crate::relation::OracleId,
    omega_lay: &crate::relation::VectorLay,
) -> crate::relation::Row {
    use crate::relation::{Part, Row, RowKind};
    use crate::tensor::{tensor_below, Tensor};
    let k_row = s.k_row();
    let mut row = Row::new("LIN: Omega against the folded row", RowKind::Plain);
    let mut cut = Vec::new();
    tensor_below(
        &Tensor::eq(&zeta[..k_row as usize], E::ONE),
        0,
        k_row,
        s.matrix_rows,
        &mut cut,
    );
    for t in cut.drain(..) {
        row.add(omega, Part::Main, omega_lay.on_table(t));
    }
    let mut on_u = Tensor::eq(&psi[..s.k_lo as usize], E::ZERO - E::ONE);
    for &z in &zeta[..k_row as usize] {
        on_u.push(E::ONE - z, z);
    }
    tensor_below(&on_u, s.k_lo, k_row, s.matrix_rows, &mut cut);
    for t in cut {
        row.add(u, Part::Main, u_lay.on_table(t));
    }
    row
}
