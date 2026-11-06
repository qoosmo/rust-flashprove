//! Multilinear helpers over E (`blocks/field/mle.h`).
//!
//! $\mathrm{eq}(j, z) = \prod_{t<k} \big(j_t z_t + (1-j_t)(1-z_t)\big)$, with $j_t$
//! bit $t$ of $j$ (bit 0 first).

use flashprove_field::{Ext3 as E, Fp};

/// `eq_table`: out[j] = eq(j, z) for j < 2^k.
pub fn eq_table(z: &[E], k: u32) -> Vec<E> {
    assert!(
        z.len() >= k as usize,
        "eq_table: fewer coordinates than variables"
    );
    let mut out = vec![E::ZERO; 1 << k];
    out[0] = E::ONE;
    for (t, &zt) in z.iter().enumerate().take(k as usize) {
        let half = 1 << t;
        for j in 0..half {
            let hi = out[j] * zt;
            out[j + half] = hi;
            out[j] -= hi;
        }
    }
    out
}

/// `eq_index`: eq(j, z) for one index; bits of j from bit k up are ignored.
pub fn eq_index(j: u64, z: &[E], k: u32) -> E {
    assert!(
        z.len() >= k as usize,
        "eq_index: fewer coordinates than variables"
    );
    let mut r = E::ONE;
    for (t, &zt) in z.iter().enumerate().take(k as usize) {
        r *= if (j >> t) & 1 == 1 { zt } else { E::ONE - zt };
    }
    r
}

/// $\sum_i a_i b_i$ for b over F.
pub fn inner_base(a: &[E], b: &[Fp]) -> E {
    assert_eq!(a.len(), b.len(), "inner product of unequal lengths");
    a.iter().zip(b).fold(E::ZERO, |s, (x, &y)| s + x.scale(y))
}
/// $\sum_i a_i b_i$ over E.
pub fn inner(a: &[E], b: &[E]) -> E {
    assert_eq!(a.len(), b.len(), "inner product of unequal lengths");
    a.iter().zip(b).fold(E::ZERO, |s, (&x, &y)| s + x * y)
}
/// `product_index`: $\prod_{i < \text{count},\ \text{bit } i \text{ of } j} f_i$.
pub fn product_index(f: &[Fp], count: u32, j: u64) -> Fp {
    let mut r = Fp::ONE;
    for (i, &fi) in f.iter().enumerate().take(count as usize) {
        if (j >> i) & 1 == 1 {
            r *= fi;
        }
    }
    r
}

#[cfg(test)]
mod tests {
    use super::*;

    fn e(a: u64, b: u64, c: u64) -> E {
        E([
            Fp::from_canonical(a).unwrap(),
            Fp::from_canonical(b).unwrap(),
            Fp::from_canonical(c).unwrap(),
        ])
    }

    #[test]
    fn eq_table_agrees_with_eq_index_and_sums_to_one() {
        let z = [e(3, 1, 4), e(1, 5, 9), e(2, 6, 5), e(3, 5, 8)];
        let t = eq_table(&z, 4);
        for (j, v) in t.iter().enumerate() {
            assert_eq!(*v, eq_index(j as u64, &z, 4));
        }
        // sum_j eq(j, z) = prod_t ((1 - z_t) + z_t) = 1.
        assert_eq!(t.iter().fold(E::ZERO, |s, &x| s + x), E::ONE);
        // On a point of the cube, eq is the indicator.
        let cube = [E::ONE, E::ZERO, E::ONE];
        let t = eq_table(&cube, 3);
        assert!(t
            .iter()
            .enumerate()
            .all(|(j, v)| *v == if j == 0b101 { E::ONE } else { E::ZERO }));
    }

    #[test]
    fn products_and_inner() {
        let f = [
            Fp::from_canonical(2).unwrap(),
            Fp::from_canonical(3).unwrap(),
            Fp::from_canonical(5).unwrap(),
        ];
        assert_eq!(product_index(&f, 3, 0b101).value(), 10);
        assert_eq!(
            product_index(&f, 2, 0b101).value(),
            2,
            "bits from count up are ignored"
        );
        assert_eq!(
            inner_base(&[e(1, 2, 3), e(4, 5, 6)], &[f[0], f[1]]),
            e(14, 19, 24)
        );
        assert_eq!(
            inner(&[E::ONE, e(0, 1, 0)], &[e(7, 0, 0), e(0, 1, 0)]),
            e(7, 0, 1)
        );
    }
}
