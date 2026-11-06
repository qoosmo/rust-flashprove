//! FOLD, verifier side (`blocks/iop/fold.h`, `fold_rounds.h`, `fold_algebra.h`).
//!
//! FOLD reduces a claim $\langle c, m\rangle + \langle d, \mu\rangle = t$ on a group's $2^k$
//! main rows and $2^h$ mask rows to a claim on single rows (the main rows folded at
//! $g_1..g_k$, the old and the fresh mask rows folded at $g_1..g_h$).
//!
//! Messages: the hiding sum $\sigma$ (with the FOLD $\varepsilon$ round), then $k$ rounds each
//! sending $(c_0, c_2)$, followed by the draw $g_j$. The running claim starts at
//! $\sigma + \varepsilon t$; in each round $c_1$ is fixed by $q(0) + q(1) = \text{claim}$, i.e.
//! $c_1 = \text{claim} - 2c_0 - c_2$, and the claim becomes $q(g_j) = c_0 + c_1 g_j + c_2 g_j^2$.
//! No equation is tested here; the blocks after FOLD reject a false claim.

use flashprove_field::Ext3 as E;

use crate::code::{ceil_log2, Codes};
use crate::relation::{GroupLayout, GroupRow, KeptForm, OracleId, Statement};
use crate::tensor::Form;

/// `FoldVerifierRounds`: the running claim.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FoldVerifierRounds {
    claim: E,
}
impl FoldVerifierRounds {
    /// Starts at $\sigma + \varepsilon\,t$.
    pub fn new(mask_sum: E, eps: E, target: E) -> Self {
        Self {
            claim: mask_sum + eps * target,
        }
    }
    /// One round: $c_1$ from $\phi(q) = q(0) + q(1) = \text{claim}$ (`Weight::plain(3)`), then
    /// $\text{claim} \leftarrow q(g)$.
    pub fn round(&mut self, c0: E, c2: E, g: E) {
        let two = E::ONE + E::ONE;
        let c1 = self.claim - (two * c0 + c2);
        self.claim = (c2 * g + c1) * g + c0;
    }
    pub fn claim(&self) -> E {
        self.claim
    }
}

/// `fold_low`: folds the first `count` variables, $v_i \leftarrow v_{2i} + g (v_{2i+1} - v_{2i})$.
pub fn fold_low(mut v: Vec<E>, g: &[E], count: u32) -> Vec<E> {
    for &gj in g.iter().take(count as usize) {
        assert!(v.len() % 2 == 0, "fold_low_once: an odd number of rows");
        let half = v.len() / 2;
        for i in 0..half {
            v[i] = v[2 * i] + gj * (v[2 * i + 1] - v[2 * i]);
        }
        v.truncate(half);
    }
    v
}

/// `fold_mask_columns`: $2k + 1 - h$.
pub fn fold_mask_columns(k: u32, h: u32) -> u64 {
    2 * k as u64 + 1 - h as u64
}

/// `fold_mask_form`: the claim's $d$ folded at $g_1..g_h$, times $\varepsilon \prod_{t \ge h} g_t$.
pub fn fold_mask_form(k: u32, h: u32, d: Vec<E>, eps: E, g: &[E]) -> Vec<E> {
    assert!(g.len() == k as usize && h <= k, "fold_mask_form: bad shape");
    let mut d = fold_low(d, g, h);
    let mut s = eps;
    for &gt in &g[h as usize..k as usize] {
        s *= gt;
    }
    for x in &mut d {
        *x *= s;
    }
    d
}

/// `fold_mask_weights`: $u(g)$ with $U(g) = \langle u(g), \text{fresh mask folded}\rangle$.
pub fn fold_mask_weights(k: u32, h: u32, len: u64, g: &[E]) -> Vec<E> {
    assert!(
        k >= 1 && h <= k && g.len() == k as usize,
        "fold_mask_weights: bad shape"
    );
    assert!(
        len >= fold_mask_columns(k, h),
        "fold_mask_weights: the rows are too short"
    );
    let (k, h) = (k as usize, h as usize);
    let mut after = vec![E::ONE; k + 1]; // after[l] = prod_{j > l} g_j, variables from 1
    for l in (0..k).rev() {
        after[l] = after[l + 1] * g[l];
    }
    let mut u = vec![E::ZERO; len as usize];
    u[0] = after[h];
    for l in 1..=h {
        u[l] = g[l - 1] * after[h];
    }
    let mut col = h + 1;
    for l in h + 1..=k {
        let from = if l == h + 1 { 2 } else { 1 };
        for t in from..=2 {
            let gl = g[l - 1];
            u[col] = if t == 1 { gl } else { gl * gl } * after[l];
            col += 1;
        }
    }
    if h < k {
        u[col] = E::ONE;
    }
    u
}

/// `fold_kept_factor`: $\varepsilon \prod_j (1 - g_j)$.
pub fn fold_kept_factor(eps: E, g: &[E]) -> E {
    g.iter().fold(eps, |s, &x| s * (E::ONE - x))
}

/// `FoldShape` (verifier side): codes and layout; for IOPP, `iopp_fold_shape` overrides the
/// layout's k and h with the stage's.
#[derive(Debug, Clone)]
pub struct FoldShape {
    pub code: u32,
    pub mask_code: u32,
    pub layout: GroupLayout,
}

/// `SingleRows`, verifier side.
#[derive(Debug, Clone)]
pub struct SingleRows {
    pub code: u32,
    pub mask_code: u32,
    pub layout: GroupLayout,
    pub gamma: Vec<E>,
    pub masks: u32,
    pub fresh: OracleId,
    pub c: Form,
    pub kept: Vec<KeptForm>,
    pub d: Vec<Vec<E>>,
    pub target: E,
    pub kept_rows: u64,
}

/// `fold_shape_check`; an error is a program fault upstream (`BLK_REQUIRE`).
pub fn fold_shape_check(st: &Statement, s: &FoldShape) -> Result<(), &'static str> {
    let codes = st.codes();
    let l = &s.layout;
    let (Some(b), Some(m)) = (
        codes.base.get(s.code as usize),
        codes.mask.get(s.mask_code as usize),
    ) else {
        return Err("FOLD: the shape names a code that does not exist");
    };
    if !(l.k >= 1 && l.h <= l.k) {
        return Err("FOLD: no row variable, or more mask rows than main rows");
    }
    if m.log_n > b.log_n {
        return Err("FOLD: the mask code is longer than the main code");
    }
    if m.ell < fold_mask_columns(l.k, l.h) {
        return Err("FOLD: the mask rows are too short for the hiding polynomial");
    }
    let n = l.members.len();
    if l.kept.len() != n || l.main_first.len() != n || l.mask_first.len() != n {
        return Err("FOLD: the layout's lists do not have one entry for each member");
    }
    let mut folds_something = false;
    for i in 0..n {
        let o = &st.oracle(l.members[i]).shape;
        let folded = o.main_rows > 0 && !l.kept[i];
        folds_something |= folded;
        if o.main_rows > 0 && o.code != Some(s.code) {
            return Err("FOLD: a member's main rows are under another code than the group's");
        }
        if o.mask_rows > 0 && o.mask_code != Some(s.mask_code) {
            return Err("FOLD: a member's mask rows are under another code than the group's");
        }
        let main_ok = if folded {
            l.main_first[i] != GroupLayout::NONE && l.main_first[i] + o.main_rows <= 1 << l.k
        } else {
            l.main_first[i] == GroupLayout::NONE
        };
        if !main_ok {
            return Err("FOLD: a member's main rows do not lie among the group's 2^k rows, or rows that are not folded have a place there");
        }
        let mask_ok = if o.mask_rows > 0 {
            l.mask_first[i] != GroupLayout::NONE && l.mask_first[i] + o.mask_rows <= 1 << l.h
        } else {
            l.mask_first[i] == GroupLayout::NONE
        };
        if !mask_ok {
            return Err("FOLD: a member's mask rows do not lie among the group's 2^h rows, or a member without mask rows has a place there");
        }
    }
    if !folds_something {
        return Err("FOLD: no member of the group has a main row to fold");
    }
    Ok(())
}

/// `fold_row_check`.
pub fn fold_row_check(st: &Statement, s: &FoldShape, row: &GroupRow) -> Result<(), &'static str> {
    let codes = st.codes();
    if !row
        .c
        .fits(s.layout.k + ceil_log2(codes.base[s.code as usize].ell))
    {
        return Err(
            "FOLD: the claim's coefficients on the main rows have not the main table's length",
        );
    }
    if row.d.len() as u64 != codes.mask[s.mask_code as usize].ell << s.layout.h {
        return Err(
            "FOLD: the claim's coefficients on the mask rows have not the mask table's length",
        );
    }
    for f in &row.kept {
        let i = s
            .layout
            .members
            .iter()
            .position(|&m| m == f.oracle)
            .ok_or("FOLD: the claim names a non-member")?;
        if !s.layout.kept[i] {
            return Err("FOLD: the claim has separate coefficients on a member that is not kept");
        }
        if !f
            .c
            .fits(st.table_bits(f.oracle, crate::relation::Part::Main))
        {
            return Err(
                "FOLD: the claim's coefficients on a kept member have not its table's length",
            );
        }
    }
    Ok(())
}

/// `fold_output` (verifier: `row` moved in), followed by `fold_rounds_verify`'s freeze of `c`.
pub fn fold_output(
    st: &Statement,
    s: &FoldShape,
    row: GroupRow,
    fresh: OracleId,
    eps: E,
    gamma: &[E],
    claim: E,
) -> SingleRows {
    let codes: &Codes = st.codes();
    let (k, h) = (s.layout.k, s.layout.h);
    let mut c = row.c;
    c.fix_low(gamma, k, eps);
    c.freeze(ceil_log2(codes.base[s.code as usize].ell));
    let factor = fold_kept_factor(eps, gamma);
    let mut kept = row.kept;
    for f in &mut kept {
        f.c.scale(factor);
    }
    let kept_rows = s
        .layout
        .members
        .iter()
        .zip(&s.layout.kept)
        .filter(|(_, &kp)| kp)
        .map(|(&m, _)| st.oracle(m).shape.main_rows)
        .sum();
    let d = vec![
        fold_mask_form(k, h, row.d, eps, gamma),
        fold_mask_weights(k, h, codes.mask[s.mask_code as usize].ell, gamma),
    ];
    SingleRows {
        code: s.code,
        mask_code: s.mask_code,
        layout: s.layout.clone(),
        gamma: gamma.to_vec(),
        masks: 2,
        fresh,
        c,
        kept,
        d,
        target: claim,
        kept_rows,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use flashprove_field::Fp;

    fn e(a: u64, b: u64, c: u64) -> E {
        E([
            Fp::from_canonical(a).unwrap(),
            Fp::from_canonical(b).unwrap(),
            Fp::from_canonical(c).unwrap(),
        ])
    }

    /// An honest sumcheck on a written-out table f over {0,1}^k: the rounds' running claim
    /// ends at f folded at g, from the start sum_x f(x).
    #[test]
    fn running_claim_of_an_honest_sumcheck_is_the_folded_value() {
        let k = 4;
        let f: Vec<E> = (0..16).map(|i| e(i * i + 3, i, 7 * i)).collect();
        let g = [e(4, 4, 1), e(2, 0, 3), e(7, 1, 1), e(5, 5, 5)];
        let sum = f.iter().fold(E::ZERO, |s, &x| s + x);
        // claim = sigma + eps * t with sigma = sum, eps = 0.
        let mut rounds = FoldVerifierRounds::new(sum, E::ZERO, e(9, 9, 9));
        let mut cur = f.clone();
        for &gj in g.iter().take(k) {
            // q(X) = sum_b (cur[2b] + X (cur[2b+1] - cur[2b])), degree 1: c2 = 0.
            let c0 = (0..cur.len() / 2).fold(E::ZERO, |s, b| s + cur[2 * b]);
            rounds.round(c0, E::ZERO, gj);
            cur = fold_low(cur, &[gj], 1);
        }
        assert_eq!(rounds.claim(), cur[0]);
        assert_eq!(fold_low(f, &g, 4)[0], cur[0]);
    }

    /// U(g) = <u(g), fold_mask_table(w) folded at g_1..g_h>, with U as fold_algebra.h defines
    /// it: U = sum_l w_l(X_l) prod_{j>l} X_j, w_l(X) = w_{l,0} [l = k] + w_{l,1} X + w_{l,2} X^2.
    #[test]
    fn mask_weights_read_the_hiding_polynomial() {
        for (k, h) in [(3_u32, 0_u32), (3, 2), (4, 4), (5, 3)] {
            let g: Vec<E> = (0..k as u64).map(|i| e(3 + i, 2 * i + 1, i)).collect();
            let w1: Vec<E> = (0..k as u64).map(|i| e(10 + i, 1, 0)).collect();
            let w2: Vec<E> = (0..k as u64).map(|i| e(20 + i, 0, 2)).collect();
            let wk0 = e(99, 1, 1);
            let mut u_at_g = E::ZERO;
            for l in 0..k as usize {
                let mut term = w1[l] * g[l] + w2[l] * g[l] * g[l];
                if l + 1 == k as usize {
                    term += wk0;
                }
                for &gj in &g[l + 1..] {
                    term *= gj;
                }
                u_at_g += term;
            }
            // The table as fold_mask_table writes it, folded at g_1..g_h.
            let len = fold_mask_columns(k, h) as usize + 2;
            let rows = 1_usize << h;
            let mut table = vec![E::ZERO; rows * len];
            for b in 0..rows {
                let at = |col: usize| b + rows * col;
                table[at(0)] = if h < k { w1[h as usize] } else { wk0 };
                let mut l = h as usize;
                while l >= 1 && (b >> (l - 1)) & 1 == 1 {
                    table[at(0)] += w1[l - 1];
                    table[at(l)] = w2[l - 1];
                    l -= 1;
                }
                let mut col = h as usize + 1;
                for l in h as usize + 1..=k as usize {
                    let from = if l == h as usize + 1 { 2 } else { 1 };
                    for t in from..=2 {
                        table[at(col)] = if t == 1 { w1[l - 1] } else { w2[l - 1] };
                        col += 1;
                    }
                }
                if h < k {
                    table[at(col)] = wk0;
                }
            }
            let folded: Vec<E> = (0..len)
                .map(|col| fold_low(table[col * rows..(col + 1) * rows].to_vec(), &g, h)[0])
                .collect();
            let u = fold_mask_weights(k, h, len as u64, &g);
            let ip = u.iter().zip(&folded).fold(E::ZERO, |s, (&a, &b)| s + a * b);
            assert_eq!(ip, u_at_g, "k {k}, h {h}");
        }
    }
}
