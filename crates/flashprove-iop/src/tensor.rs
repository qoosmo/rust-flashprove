//! Structured coefficient vectors (`blocks/iop/tensor.h`): [`Tensor`] and [`Form`].
//!
//! Index convention: an index $j < 2^a$ has bits $j_0$ (least significant) to $j_{a-1}$;
//! variable $t$ is bit $t$. A table of $2^k$ rows of length $l$ is the vector with entry $c$
//! of row $b$ at index $b + 2^k c$.
//!
//! A [`Tensor`] on $a$ variables is
//! $v[j] = s \prod_{t<a} (j_t\,?\,h_t : l_t) \cdot B[\mathrm{first} + d(j)]$,
//! with the dense factor $B$ optional and $d(j)$ the bits of $j$ at the dense variables.
//! A variable whose pair is $(1,0)$ or $(0,1)$ is a choice variable, stored as two bit masks.
//!
//! Verifier side only: no engine tables (`held`), no engine terms, no hints. Every function
//! computes the same field elements as the reference; the order of products may differ,
//! which exact field arithmetic does not see. A violated precondition is a program fault
//! (`BLK_REQUIRE`) and panics.

use std::collections::BTreeMap;
use std::sync::Arc;

use flashprove_field::{Ext3 as E, Fp};

/// `lies_in_F`.
pub fn lies_in_f(a: &E) -> bool {
    a.0[1] == Fp::ZERO && a.0[2] == Fp::ZERO
}
/// `times(a, b)`: $ab$.
pub fn times(a: E, b: E) -> E {
    if lies_in_f(&b) {
        a.scale(b.0[0])
    } else {
        a * b
    }
}
fn is_zero(a: &E) -> bool {
    *a == E::ZERO
}
fn low_mask(count: u32) -> u64 {
    if count < 64 {
        (1_u64 << count) - 1
    } else {
        !0
    }
}

/// `Tensor`.
#[derive(Debug, Clone)]
pub struct Tensor {
    pub scalar: E,
    /// Variables indexing the dense factor; bit $i$ of $d$ is bit `dense_vars[i]` of the index.
    pub dense_vars: Vec<u32>,
    pub values: Option<Arc<Vec<E>>>,
    pub first: u64,
    /// (lo, hi) of the real variables, in their order; shared between copies.
    pairs: Arc<Vec<(E, E)>>,
    from: usize,
    vars: u32,
    pick_mask: u64,
    pick_value: u64,
}
impl Default for Tensor {
    fn default() -> Self {
        Self {
            scalar: E::ONE,
            dense_vars: Vec::new(),
            values: None,
            first: 0,
            pairs: Arc::new(Vec::new()),
            from: 0,
            vars: 0,
            pick_mask: 0,
            pick_value: 0,
        }
    }
}

/// `Tensor::Slice`: a folded dense factor.
#[derive(Debug, Clone)]
pub struct Slice {
    pub values: Arc<Vec<E>>,
    pub factor: E,
}

impl Tensor {
    pub fn vars(&self) -> u32 {
        self.vars
    }
    pub fn has_dense(&self) -> bool {
        !self.dense_vars.is_empty()
    }
    pub fn picks(&self, t: u32) -> bool {
        (self.pick_mask >> t) & 1 == 1
    }
    pub fn pick_mask(&self) -> u64 {
        self.pick_mask
    }
    pub fn pick_value(&self) -> u64 {
        self.pick_value
    }
    fn reals(&self) -> usize {
        self.vars as usize - self.pick_mask.count_ones() as usize
    }
    fn real_at(&self, t: u32) -> usize {
        self.from + (!self.pick_mask & low_mask(t)).count_ones() as usize
    }
    /// The pair of variable t.
    pub fn lo(&self, t: u32) -> E {
        if self.picks(t) {
            if (self.pick_value >> t) & 1 == 1 {
                E::ZERO
            } else {
                E::ONE
            }
        } else {
            self.pairs[self.real_at(t)].0
        }
    }
    pub fn hi(&self, t: u32) -> E {
        if self.picks(t) {
            if (self.pick_value >> t) & 1 == 1 {
                E::ONE
            } else {
                E::ZERO
            }
        } else {
            self.pairs[self.real_at(t)].1
        }
    }

    /// `Tensor::eq`: $s \cdot \mathrm{eq}(\cdot, z)$ on `z.len()` variables.
    pub fn eq(z: &[E], scalar: E) -> Self {
        let mut v = Self {
            scalar,
            ..Self::default()
        };
        for &zt in z {
            v.push(E::ONE - zt, zt);
        }
        v
    }
    /// `Tensor::product`: $(s \prod_{t:\, j_t = 1} f_t)_j$.
    pub fn product(f: &[Fp], scalar: E) -> Self {
        let mut v = Self {
            scalar,
            ..Self::default()
        };
        for &ft in f {
            v.push(E::ONE, E::from_base(ft));
        }
        v
    }
    fn own_pairs(&mut self) {
        let end = self.from + self.reals();
        if Arc::strong_count(&self.pairs) > 1 || self.pairs.len() != end {
            self.pairs = Arc::new(self.pairs[self.from..end].to_vec());
            self.from = 0;
        }
    }
    /// `push`: appends a new highest variable with the pair (l, h).
    pub fn push(&mut self, l: E, h: E) {
        assert!(self.vars < 63, "tensor: more than 63 variables");
        let (l0, h0) = (is_zero(&l), is_zero(&h));
        if (l0 && h == E::ONE) || (h0 && l == E::ONE) {
            self.pick_mask |= 1 << self.vars;
            if l0 {
                self.pick_value |= 1 << self.vars;
            }
        } else {
            self.own_pairs();
            Arc::get_mut(&mut self.pairs)
                .expect("own_pairs leaves one owner")
                .push((l, h));
        }
        self.vars += 1;
    }
    fn rebuild(&mut self, los: &[E], his: &[E]) {
        self.pairs = Arc::new(Vec::new());
        self.from = 0;
        self.vars = 0;
        self.pick_mask = 0;
        self.pick_value = 0;
        for (l, h) in los.iter().zip(his) {
            self.push(*l, *h);
        }
    }
    /// `set_pair`.
    pub fn set_pair(&mut self, t: u32, l: E, h: E) {
        let los: Vec<E> = (0..self.vars)
            .map(|i| if i == t { l } else { self.lo(i) })
            .collect();
        let his: Vec<E> = (0..self.vars)
            .map(|i| if i == t { h } else { self.hi(i) })
            .collect();
        self.rebuild(&los, &his);
    }
    /// `rotate`: variable t becomes variable (t + vars - by) mod vars. `dense_vars` is left
    /// to the caller.
    pub fn rotate(&mut self, by: u32) {
        let n = self.vars;
        let los: Vec<E> = (0..n).map(|i| self.lo((i + by) % n)).collect();
        let his: Vec<E> = (0..n).map(|i| self.hi((i + by) % n)).collect();
        self.rebuild(&los, &his);
    }
    /// `push_dense`.
    pub fn push_dense(&mut self, count: u32) {
        assert!(
            self.values.is_none(),
            "tensor: a dense variable is added after the slice was fixed"
        );
        for _ in 0..count {
            self.dense_vars.push(self.vars);
            self.push(E::ONE, E::ONE);
        }
    }
    fn dense_check(&self, first: u64, length: u64) {
        assert!(
            self.dense_vars.len() < 64
                && first <= length
                && (1_u64 << self.dense_vars.len()) <= length - first,
            "tensor: the slice does not lie in the vector"
        );
        for (i, &d) in self.dense_vars.iter().enumerate() {
            assert!(
                d < self.vars && self.lo(d) == E::ONE && self.hi(d) == E::ONE,
                "tensor: a dense variable does not exist, or has another pair than (1, 1)"
            );
            assert!(
                !self.dense_vars[..i].contains(&d),
                "tensor: a variable is dense twice"
            );
        }
    }
    /// `set_values`.
    pub fn set_values(&mut self, values: Arc<Vec<E>>, first: u64) {
        assert!(
            !self.dense_vars.is_empty(),
            "tensor: a slice for a tensor without dense variables"
        );
        self.dense_check(first, values.len() as u64);
        self.values = Some(values);
        self.first = first;
    }
    fn factor_check(&self) {
        assert!(
            self.dense_vars.is_empty() || self.values.is_some(),
            "tensor: dense variables without a vector"
        );
    }
    fn dense_index(&self, j: u64) -> u64 {
        self.dense_vars
            .iter()
            .enumerate()
            .fold(0, |d, (i, &v)| d | (((j >> v) & 1) << i))
    }
    /// `insert_choice`: inserts, before variable `at`, `count` choice variables fixing their
    /// bits to `value` (bits of `value` from `count` up are ignored).
    pub fn insert_choice(&mut self, at: u32, count: u32, value: u64) {
        assert!(at <= self.vars, "tensor: no such variable");
        assert!(
            count <= 63 && self.vars + count <= 63,
            "tensor: more than 63 variables"
        );
        if count == 0 {
            return;
        }
        let low = (1_u64 << at) - 1;
        let ones = (1_u64 << count) - 1;
        self.pick_mask = (self.pick_mask & low) | ((self.pick_mask & !low) << count) | (ones << at);
        self.pick_value =
            (self.pick_value & low) | ((self.pick_value & !low) << count) | ((value & ones) << at);
        self.vars += count;
        for d in &mut self.dense_vars {
            if *d >= at {
                *d += count;
            }
        }
    }
    /// `at`: entry j.
    pub fn at(&self, j: u64) -> E {
        self.factor_check();
        if j & self.pick_mask != self.pick_value {
            return E::ZERO;
        }
        let mut r = self.scalar;
        let mut pair = self.from;
        for t in 0..self.vars {
            if !self.picks(t) {
                let (l, h) = self.pairs[pair];
                pair += 1;
                r *= if (j >> t) & 1 == 1 { h } else { l };
            }
        }
        match &self.values {
            Some(b) if self.has_dense() && !is_zero(&r) => {
                r * b[(self.first + self.dense_index(j)) as usize]
            }
            _ => r,
        }
    }
    /// `mle`: $\sum_j \mathrm{eq}(j, x)\, v[j]$ for x of `vars()` coordinates.
    pub fn mle(&self, x: &[E]) -> E {
        let mut v = self.clone();
        v.fix_low(x, self.vars, None);
        v.scalar
    }
    /// `slice_is_cut`.
    pub fn slice_is_cut(&self, count: u32) -> bool {
        self.dense_vars.iter().any(|&d| d < count)
    }
    /// `folded_slice`: the dense factor with its dense variables below `count` fixed at g.
    pub fn folded_slice(&self, g: &[E], count: u32) -> Slice {
        let values = self
            .values
            .as_ref()
            .expect("tensor: dense variables without a vector");
        let mut n = 1_usize << self.dense_vars.len();
        let first = self.first as usize;
        assert!(
            first <= values.len() && n <= values.len() - first,
            "tensor: a written-out slice reaches beyond its vector"
        );
        let mut cur: Vec<E> = values[first..first + n].to_vec();
        for i in (0..self.dense_vars.len()).rev() {
            if self.dense_vars[i] >= count {
                continue;
            }
            let x = g[self.dense_vars[i] as usize];
            let low_half = 1_usize << i;
            let mut to = vec![E::ZERO; n / 2];
            for b in 0..n / (2 * low_half) {
                for a in 0..low_half {
                    let zero = cur[a + 2 * low_half * b];
                    let one = cur[a + low_half + 2 * low_half * b];
                    to[a + low_half * b] = zero + (one - zero) * x;
                }
            }
            cur = to;
            n /= 2;
        }
        let factor = if n == 1 { cur[0] } else { E::ONE };
        Slice {
            values: Arc::new(cur),
            factor,
        }
    }
    /// `fix_low`: entry j becomes $\sum_i \mathrm{eq}(i, g)\, v[i + 2^{\text{count}} j]$.
    /// `ready`: the folded slice, if the caller has it.
    pub fn fix_low(&mut self, g: &[E], count: u32, ready: Option<&Slice>) {
        assert!(
            count <= self.vars,
            "tensor: more variables fixed than there are"
        );
        self.factor_check();
        let low = low_mask(count);
        let (mask, value) = (self.pick_mask & low, self.pick_value & low);
        for t in 0..count {
            if (mask >> t) & 1 == 1 {
                self.scalar *= if (value >> t) & 1 == 1 {
                    g[t as usize]
                } else {
                    E::ONE - g[t as usize]
                };
                continue;
            }
            let (l, h) = self.pairs[self.from];
            self.from += 1;
            if l == E::ONE && h == E::ONE {
                continue; // a dense variable, or no weight on this variable
            }
            self.scalar *= l + g[t as usize] * (h - l);
        }
        let cut = self.slice_is_cut(count);
        let s = if self.has_dense() && cut {
            Some(match ready {
                Some(s) => s.clone(),
                None => self.folded_slice(g, count),
            })
        } else {
            None
        };
        self.pick_mask = if count < 64 {
            self.pick_mask >> count
        } else {
            0
        };
        self.pick_value = if count < 64 {
            self.pick_value >> count
        } else {
            0
        };
        self.vars -= count;
        if !self.has_dense() {
            return;
        }
        if let Some(s) = s {
            self.dense_vars.retain(|&d| d >= count);
            if self.dense_vars.is_empty() {
                self.scalar *= s.factor;
                self.values = None;
            } else {
                self.values = Some(s.values);
            }
            self.first = 0;
        }
        for d in &mut self.dense_vars {
            *d -= count;
        }
    }
    /// `add_to`: adds all $2^{\text{vars}}$ entries to `out`.
    pub fn add_to(&self, out: &mut [E]) {
        self.factor_check();
        assert!(
            out.len() as u64 >= 1_u64 << self.vars,
            "tensor: the output is shorter than the vector"
        );
        let real = self.reals();
        let mut v = vec![E::ZERO; 1 << real];
        v[0] = self.scalar;
        for r in 0..real {
            let half = 1 << r;
            let (l, h) = self.pairs[self.from + r];
            for j in 0..half {
                v[j + half] = v[j] * h;
                v[j] *= l;
            }
        }
        let places = !self.pick_mask & low_mask(self.vars);
        let mut at: u64 = 0;
        for &vj in &v {
            let index = at | self.pick_value;
            let add = match &self.values {
                Some(b) if self.has_dense() => {
                    vj * b[(self.first + self.dense_index(index)) as usize]
                }
                _ => vj,
            };
            out[index as usize] += add;
            at = at.wrapping_sub(places) & places;
        }
    }
    /// `part`: the factor on variables from..from+count, written out, without the scalar
    /// and the dense factor.
    pub fn part(&self, from: u32, count: u32) -> Vec<E> {
        assert!(
            from <= self.vars && count <= self.vars - from,
            "tensor: a part beyond the variables"
        );
        let mut w = vec![E::ZERO; 1 << count];
        w[0] = E::ONE;
        for t in 0..count {
            let half = 1 << t;
            let (l, h) = (self.lo(from + t), self.hi(from + t));
            for j in 0..half {
                w[j + half] = w[j] * h;
                w[j] *= l;
            }
        }
        w
    }
}

/// `FrozenPart`: $s \cdot f$ under choice variables, $f$ a shared Form on `vars` variables.
#[derive(Debug, Clone)]
pub struct FrozenPart {
    pub form: Arc<Form>,
    pub vars: u32,
    pub scale: E,
    pub choice_mask: u64,
    pub choice_value: u64,
}

/// `Form`: a sum of tensors, single entries (an index may repeat) and frozen parts.
#[derive(Debug, Clone, Default)]
pub struct Form {
    pub tensors: Vec<Tensor>,
    pub entries: Vec<(u64, E)>,
    pub frozen: Vec<FrozenPart>,
}

/// `Form::without_bits`: the index formed by the bits of j outside mask, in their order.
pub fn without_bits(j: u64, mask: u64) -> u64 {
    let mut inner = 0;
    let mut i = 0;
    for t in 0..64 {
        if (mask >> t) & 1 == 0 {
            inner |= ((j >> t) & 1) << i;
            i += 1;
        }
    }
    inner
}
fn frozen_fits(p: &FrozenPart, vars: u32) -> bool {
    vars < 64 && p.choice_mask >> vars == 0 && p.vars + p.choice_mask.count_ones() == vars
}

impl Form {
    pub fn is_empty(&self) -> bool {
        self.tensors.is_empty() && self.entries.is_empty() && self.frozen.is_empty()
    }
    pub fn add(&mut self, v: Tensor) {
        self.tensors.push(v);
    }
    pub fn add_entry(&mut self, index: u64, coefficient: E) {
        self.entries.push((index, coefficient));
    }
    /// `add(other, x)`: this += x * other.
    pub fn add_form(&mut self, other: Form, x: E) {
        for mut v in other.tensors {
            v.scalar *= x;
            self.tensors.push(v);
        }
        for (i, c) in other.entries {
            self.entries.push((i, c * x));
        }
        for mut p in other.frozen {
            p.scale *= x;
            self.frozen.push(p);
        }
    }
    pub fn scale(&mut self, x: E) {
        for v in &mut self.tensors {
            v.scalar *= x;
        }
        for e in &mut self.entries {
            e.1 *= x;
        }
        for p in &mut self.frozen {
            p.scale *= x;
        }
    }
    /// `freeze`: the whole Form, on `vars` variables, becomes one frozen part.
    pub fn freeze(&mut self, vars: u32) {
        assert!(
            self.fits(vars),
            "form: a part does not fit a vector of this many variables"
        );
        let all = Form {
            tensors: std::mem::take(&mut self.tensors),
            entries: std::mem::take(&mut self.entries),
            frozen: std::mem::take(&mut self.frozen),
        };
        self.frozen.push(FrozenPart {
            form: Arc::new(all),
            vars,
            scale: E::ONE,
            choice_mask: 0,
            choice_value: 0,
        });
    }
    /// `flattened`.
    pub fn flattened(&self) -> Form {
        let mut f = self.clone();
        f.thaw();
        f
    }
    /// `thaw`: every frozen part copied out, at all depths.
    pub fn thaw(&mut self) {
        for p in std::mem::take(&mut self.frozen) {
            let mut f = p.form.flattened();
            for t in 0..64 {
                if (p.choice_mask >> t) & 1 == 1 {
                    f.insert_choice(t, 1, (p.choice_value >> t) & 1);
                }
            }
            for mut v in f.tensors {
                v.scalar *= p.scale;
                self.tensors.push(v);
            }
            for (i, c) in f.entries {
                self.entries.push((i, c * p.scale));
            }
        }
    }
    /// `at`: entry j.
    pub fn at(&self, j: u64) -> E {
        let mut r = E::ZERO;
        for v in &self.tensors {
            r += v.at(j);
        }
        for &(i, c) in &self.entries {
            if i == j {
                r += c;
            }
        }
        for p in &self.frozen {
            if j & p.choice_mask == p.choice_value {
                r += p.scale * p.form.at(without_bits(j, p.choice_mask));
            }
        }
        r
    }
    /// `mle`.
    pub fn mle(&self, x: &[E], vars: u32) -> E {
        assert!(
            self.fits(vars),
            "form: a part does not fit a vector of this many variables"
        );
        let mut f = self.clone();
        f.fix_low(x, vars, E::ONE);
        f.at(0)
    }
    /// `fix_low`: fixes the first `count` variables at g, then multiplies by `times`.
    pub fn fix_low(&mut self, g: &[E], count: u32, times: E) {
        let scaled = times != E::ONE;
        let low = low_mask(count);
        if !self.frozen.iter().all(|p| p.choice_mask & low == low) {
            self.thaw();
        }
        for p in &mut self.frozen {
            for t in 0..count {
                p.scale *= if (p.choice_value >> t) & 1 == 1 {
                    g[t as usize]
                } else {
                    E::ONE - g[t as usize]
                };
            }
            if scaled {
                p.scale *= times;
            }
            p.choice_mask = if count < 64 {
                p.choice_mask >> count
            } else {
                0
            };
            p.choice_value = if count < 64 {
                p.choice_value >> count
            } else {
                0
            };
        }
        // Each distinct cut slice is folded once.
        let mut folded: BTreeMap<(usize, u64, Vec<u32>), Slice> = BTreeMap::new();
        for v in &mut self.tensors {
            if scaled {
                v.scalar *= times;
            }
            if v.has_dense() && v.slice_is_cut(count) {
                let b = v
                    .values
                    .as_ref()
                    .expect("tensor: dense variables without a vector");
                let key = (Arc::as_ptr(b) as usize, v.first, v.dense_vars.clone());
                let s = folded
                    .entry(key)
                    .or_insert_with(|| v.folded_slice(g, count))
                    .clone();
                v.fix_low(g, count, Some(&s));
            } else {
                v.fix_low(g, count, None);
            }
        }
        for e in &mut self.entries {
            for t in 0..count {
                e.1 *= if (e.0 >> t) & 1 == 1 {
                    g[t as usize]
                } else {
                    E::ONE - g[t as usize]
                };
            }
            e.1 *= times;
            e.0 = if count < 64 { e.0 >> count } else { 0 };
        }
        self.merge_entries();
    }
    /// `merge_entries`: entries with the same index summed, sorted by index.
    pub fn merge_entries(&mut self) {
        if self.entries.len() < 2 {
            return;
        }
        let mut sum: BTreeMap<u64, E> = BTreeMap::new();
        for &(i, c) in &self.entries {
            *sum.entry(i).or_insert(E::ZERO) += c;
        }
        self.entries = sum.into_iter().collect();
    }
    /// `insert_choice`.
    pub fn insert_choice(&mut self, at: u32, count: u32, value: u64) {
        assert!(
            at + count < 64 && value >> count == 0,
            "form: the value has more bits than are inserted, or an index would pass 63 bits"
        );
        let low = (1_u64 << at) - 1;
        let widen = |j: u64| (j & low) | ((j & !low) << count);
        for v in &mut self.tensors {
            v.insert_choice(at, count, value);
        }
        for e in &mut self.entries {
            e.0 = widen(e.0) | (value << at);
        }
        for p in &mut self.frozen {
            p.choice_mask = widen(p.choice_mask) | (((1_u64 << count) - 1) << at);
            p.choice_value = widen(p.choice_value) | (value << at);
        }
    }
    /// `add_to`: adds all $2^{\text{vars}}$ entries to `out`.
    pub fn add_to(&self, out: &mut [E], vars: u32) {
        for v in &self.tensors {
            assert!(
                v.vars() == vars,
                "form: a tensor with another number of variables"
            );
            v.add_to(out);
        }
        for &(i, c) in &self.entries {
            assert!(i >> vars == 0, "form: an entry beyond the vector's length");
            out[i as usize] += c;
        }
        for p in &self.frozen {
            assert!(
                frozen_fits(p, vars),
                "form: a frozen part with another number of variables"
            );
            let mut inner = vec![E::ZERO; 1 << p.vars];
            p.form.add_to(&mut inner, p.vars);
            for j in 0..1_u64 << vars {
                if j & p.choice_mask == p.choice_value {
                    out[j as usize] += p.scale * inner[without_bits(j, p.choice_mask) as usize];
                }
            }
        }
    }
    /// `fits`.
    pub fn fits(&self, vars: u32) -> bool {
        self.frozen.iter().all(|p| frozen_fits(p, vars))
            && self.tensors.iter().all(|v| v.vars() == vars)
            && self
                .entries
                .iter()
                .all(|&(i, _)| vars >= 64 || i >> vars == 0)
    }
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
    fn dense(v: &Tensor) -> Vec<E> {
        (0..1_u64 << v.vars()).map(|j| v.at(j)).collect()
    }
    fn dense_form(f: &Form, vars: u32) -> Vec<E> {
        (0..1_u64 << vars).map(|j| f.at(j)).collect()
    }
    /// Reference fold of a written-out vector: entry j becomes sum_i eq(i, g) v[i + 2^count j].
    fn fold(v: &[E], g: &[E], count: u32) -> Vec<E> {
        let w = crate::ext::eq_table(g, count);
        (0..v.len() >> count)
            .map(|j| (0..1 << count).fold(E::ZERO, |s, i| s + w[i] * v[i + (j << count)]))
            .collect()
    }
    /// A tensor on 6 variables: real pairs, one choice, two dense variables.
    fn sample() -> Tensor {
        let mut v = Tensor::eq(&[e(3, 1, 4), e(1, 5, 9)], e(2, 7, 1));
        v.push_dense(2);
        v.push(E::ONE, e(6, 0, 0));
        v.insert_choice(1, 1, 1);
        let b: Vec<E> = (0..6).map(|i| e(i + 1, 2 * i, 0)).collect();
        v.set_values(Arc::new(b), 1);
        v
    }

    #[test]
    fn at_add_to_and_part_agree() {
        let v = sample();
        assert_eq!(v.vars(), 6);
        let mut out = vec![E::ZERO; 64];
        v.add_to(&mut out);
        assert_eq!(out, dense(&v));
        // Entries with the choice bit 1 at 0 vanish.
        assert!(dense(&v)
            .iter()
            .enumerate()
            .all(|(j, x)| (j >> 1) & 1 == 1 || *x == E::ZERO));
        let w = Tensor::eq(&[e(3, 1, 4), e(9, 2, 6), e(5, 3, 5)], E::ONE);
        assert_eq!(
            w.part(0, 3),
            crate::ext::eq_table(&[e(3, 1, 4), e(9, 2, 6), e(5, 3, 5)], 3)
        );
    }

    #[test]
    fn fix_low_and_mle_match_the_written_out_fold() {
        let g = [
            e(4, 4, 1),
            e(2, 0, 3),
            e(7, 1, 1),
            e(5, 5, 5),
            e(1, 2, 3),
            e(8, 0, 2),
        ];
        for count in 0..=6 {
            let mut v = sample();
            let want = fold(&dense(&v), &g, count);
            v.fix_low(&g, count, None);
            assert_eq!(dense(&v), want, "count {count}");
        }
        let v = sample();
        assert_eq!(v.mle(&g), fold(&dense(&v), &g, 6)[0]);
    }

    #[test]
    fn rotate_and_set_pair() {
        let mut v = Tensor::eq(&[e(3, 1, 4), e(1, 5, 9), e(2, 6, 5)], E::ONE);
        v.insert_choice(3, 1, 0);
        let before = dense(&v);
        let mut r = v.clone();
        r.rotate(1);
        for j in 0..16_u64 {
            // new variable t is old variable (t + 1) mod 4
            let old = ((j << 1) | (j >> 3)) & 15;
            assert_eq!(r.at(j), before[old as usize]);
        }
        v.set_pair(0, E::ONE, E::ZERO);
        assert!(v.picks(0) && v.at(1) == E::ZERO);
    }

    #[test]
    fn form_freeze_choice_and_fix_low() {
        let mut f = Form::default();
        f.add(sample());
        f.add_entry(5, e(9, 9, 9));
        f.add_entry(5, e(1, 0, 0));
        f.add_entry(40, e(2, 3, 4));
        let mut frozen = f.clone();
        frozen.freeze(6);
        frozen.insert_choice(2, 1, 1);
        f.insert_choice(2, 1, 1);
        assert_eq!(dense_form(&frozen, 7), dense_form(&f, 7));
        assert_eq!(dense_form(&frozen.flattened(), 7), dense_form(&f, 7));
        let g = [e(4, 4, 1), e(2, 0, 3), e(7, 1, 1), e(5, 5, 5)];
        let x = e(3, 0, 1);
        for count in [2, 3, 4] {
            let want: Vec<E> = fold(&dense_form(&f, 7), &g, count)
                .into_iter()
                .map(|y| y * x)
                .collect();
            let (mut a, mut b) = (f.clone(), frozen.clone());
            a.fix_low(&g, count, x);
            b.fix_low(&g, count, x);
            assert_eq!(dense_form(&a, 7 - count), want, "count {count}");
            assert_eq!(dense_form(&b, 7 - count), want, "frozen, count {count}");
            let mut out = vec![E::ZERO; 1 << (7 - count)];
            b.add_to(&mut out, 7 - count);
            assert_eq!(out, want);
        }
        let y = [
            e(1, 1, 1),
            e(2, 2, 2),
            e(3, 3, 3),
            e(4, 4, 4),
            e(5, 5, 5),
            e(6, 6, 6),
            e(7, 7, 7),
        ];
        assert_eq!(frozen.mle(&y, 7), fold(&dense_form(&f, 7), &y, 7)[0]);
    }
}
