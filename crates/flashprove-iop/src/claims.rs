//! Claims of a group and their targets, in the order a proximity test takes
//! them (`Statement::begin_run`, blocks/iop/relation.h), and the batch of
//! BAT (`Bat::combine`, blocks/iop/bat.h).
//!
//! begin_run() numbers a group's claims: its `PLAIN` claims as added; then
//! the sample claims of its member oracle messages, message by message as
//! sent; then its `GENERATOR` claims (a codeword's symbol at an opened
//! position) as added. BAT then forms $\sum_i x^i\,(\text{claim}_i)$, the
//! target included: $t = \sum_i x^i t_i$.
//!
//! This module carries targets only. The coefficient side of each claim
//! (`Row`, `GroupRow`) is in [`crate::relation`].

use flashprove_field::Ext3 as E;

/// The kind of a claim (`RowKind`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    Plain,
    Sample,
    Generator,
}

/// One claim's target, with its kind and a name for diagnostics.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Claim {
    pub kind: Kind,
    pub name: String,
    pub target: E,
}

/// The open claims of one group (`Group::rows`) and the sample claims of its
/// members, kept apart so that begin_run() can order them.
#[derive(Debug, Clone, Default)]
pub struct GroupClaims {
    rows: Vec<Claim>,
    /// Sample claims, per member oracle message in the order the members were sent.
    samples: Vec<Vec<Claim>>,
    in_run: bool,
}
impl GroupClaims {
    /// `Statement::add_row`: a plain or generator claim. Fails closed after begin_run().
    pub fn add(
        &mut self,
        kind: Kind,
        name: impl Into<String>,
        target: E,
    ) -> Result<(), &'static str> {
        if self.in_run {
            return Err("statement: a claim added to a group after its proximity test began");
        }
        if kind == Kind::Sample {
            return Err("statement: a sample claim belongs to its oracle message, not to a group");
        }
        self.rows.push(Claim {
            kind,
            name: name.into(),
            target,
        });
        Ok(())
    }
    /// The sample claims of the next member oracle message (its answers, as sent).
    pub fn add_member_samples(&mut self, name: &str, answers: &[E]) -> Result<(), &'static str> {
        if self.in_run {
            return Err("statement: a member sampled after the group's test began");
        }
        self.samples.push(
            answers
                .iter()
                .enumerate()
                .map(|(i, &a)| Claim {
                    kind: Kind::Sample,
                    name: format!("{name}: sample {i}"),
                    target: a,
                })
                .collect(),
        );
        Ok(())
    }
    /// `Statement::begin_run`: the claims in the order the test takes them. Once only.
    pub fn begin_run(&mut self) -> Result<Vec<Claim>, &'static str> {
        if self.in_run {
            return Err("statement: one proximity test for each group");
        }
        self.in_run = true;
        let mut out: Vec<Claim> = self
            .rows
            .iter()
            .filter(|c| c.kind == Kind::Plain)
            .cloned()
            .collect();
        for m in &self.samples {
            out.extend(m.iter().cloned());
        }
        out.extend(
            self.rows
                .iter()
                .filter(|c| c.kind == Kind::Generator)
                .cloned(),
        );
        self.rows.clear();
        Ok(out)
    }
}

/// BAT's target: $\sum_i x^i t_i$.
pub fn batch_target(claims: &[Claim], x: E) -> E {
    let mut power = E::ONE;
    let mut t = E::ZERO;
    for c in claims {
        t += power * c.target;
        power *= x;
    }
    t
}

/// SPLIT (`Split::finish`, blocks/iop/split.h): a claim with target t is cut in
/// two; the first group's share has the sent target $s$, the second's $t - s$.
pub fn split_targets(target: E, share: E) -> (E, E) {
    (share, target - share)
}

/// Elements of E sent in a message, each in canonical form (R8.8).
pub fn elements(bytes: &[u8]) -> Result<Vec<E>, &'static str> {
    if bytes.len() % 24 != 0 {
        return Err("a message's elements of E are not whole");
    }
    bytes
        .chunks_exact(24)
        .map(|c| E::from_le_bytes(c).map_err(|_| "an element of E not in canonical form"))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use flashprove_field::Fp;

    fn e(a: u64) -> E {
        E::from_base(Fp::from_canonical(a).unwrap())
    }

    #[test]
    fn begin_run_order_and_once() {
        let mut g = GroupClaims::default();
        g.add(Kind::Generator, "col 1", e(5)).unwrap();
        g.add(Kind::Plain, "rec 0", e(1)).unwrap();
        g.add_member_samples("u", &[e(3)]).unwrap();
        g.add(Kind::Plain, "split", e(2)).unwrap();
        g.add_member_samples("mask", &[e(4)]).unwrap();
        g.add(Kind::Generator, "col 2", e(6)).unwrap();
        let c = g.begin_run().unwrap();
        let t: Vec<u64> = c.iter().map(|c| c.target.0[0].value()).collect();
        assert_eq!(t, [1, 2, 3, 4, 5, 6]);
        assert!(g.begin_run().is_err());
        assert!(g.add(Kind::Plain, "late", e(7)).is_err());
        assert!(g.add_member_samples("late", &[e(7)]).is_err());
        // x = 2: 1 + 2*2 + 3*4 + 4*8 + 5*16 + 6*32 = 321.
        assert_eq!(batch_target(&c, e(2)), e(321));
    }

    #[test]
    fn split_and_elements() {
        assert_eq!(split_targets(e(10), e(3)), (e(3), e(7)));
        let mut b = vec![0_u8; 48];
        b[0] = 1;
        assert_eq!(elements(&b).unwrap(), vec![e(1), E::ZERO]);
        assert!(elements(&b[..47]).is_err());
        b[24..32].copy_from_slice(&flashprove_field::MODULUS.to_le_bytes());
        assert!(elements(&b).is_err());
    }
}
