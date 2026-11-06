//! SEND's sample claims, verifier side (`blocks/iop/send.h`).
//!
//! The verifier draws, per answer number $i$, a seed $(z, \beta)$ with $z \in E^{a}$ and
//! $\beta \ne 0$ (`SeedDraw::seed`: $a$ coordinates, then $\beta$ nonzero), $a$ the largest cube
//! dimension of the round's sampled oracle messages. The answer $y_i$ is the target of the claim
//! `form(o, seed_i, i)`: coefficient $\mathrm{eq}(j, z)$ (times `front`) on every entry outside
//! the pads, $\beta\theta^t$ on the pad of answer $i$, $0$ on the pads of the other answers.

use flashprove_field::Ext3 as E;

use crate::code::{ceil_log2, Codes};
use crate::relation::{OracleId, Part, Row, RowKind, Statement};
use crate::shapes::{OracleShape, E_DEGREE};
use crate::tensor::Tensor;

/// `SampleSeed`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SampleSeed {
    pub z: Vec<E>,
    pub beta: E,
}

/// `SampleCube`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct SampleCube {
    pub has_main: bool,
    pub has_mask: bool,
    pub main_row_bits: u32,
    pub main_bits: u32,
    pub mask_row_bits: u32,
    pub mask_bits: u32,
    pub bits: u32,
}

/// `PadPlace`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PadPlace {
    pub part: Part,
    pub index: u64,
    pub answer: u32,
    pub basis: E,
}

/// `Send::cube`.
pub fn cube(codes: &Codes, s: &OracleShape) -> SampleCube {
    let mut c = SampleCube {
        has_main: s.main_rows > 0,
        has_mask: s.mask_rows > 0,
        ..SampleCube::default()
    };
    if c.has_main {
        c.main_row_bits = ceil_log2(s.main_rows);
        c.main_bits = c.main_row_bits + codes.base[s.code.expect("main code") as usize].log_ell();
    }
    if c.has_mask {
        c.mask_row_bits = ceil_log2(s.mask_rows);
        c.mask_bits =
            c.mask_row_bits + codes.mask[s.mask_code.expect("mask code") as usize].log_ell();
    }
    c.bits = if c.has_main && c.has_mask {
        c.main_bits.max(c.mask_bits) + 1
    } else {
        c.main_bits + c.mask_bits
    };
    c
}

/// `Send::pad`: the last `answers` entries (three times as many over F) of the last real mask
/// row, or without mask rows of the last real main row; by increasing index.
pub fn pad(codes: &Codes, s: &OracleShape) -> Result<Vec<PadPlace>, &'static str> {
    let c = cube(codes, s);
    let (part, rows, row_bits, len) = if c.has_mask {
        (
            Part::Mask,
            s.mask_rows,
            c.mask_row_bits,
            codes.mask[s.mask_code.expect("mask code") as usize].ell,
        )
    } else {
        (
            Part::Main,
            s.main_rows,
            c.main_row_bits,
            codes.base[s.code.expect("main code") as usize].ell,
        )
    };
    let each: u64 = if c.has_mask || s.main_deg == E_DEGREE {
        1
    } else {
        E_DEGREE
    };
    let answers = s.answers as u64;
    if len < each * answers {
        return Err("send: the row is too short for the pad");
    }
    let mut places = Vec::new();
    for i in 0..s.answers {
        for t in 0..each {
            let place = len - each * answers + each * i as u64 + t;
            places.push(PadPlace {
                part,
                index: (rows - 1) + (place << row_bits),
                answer: i,
                basis: E::theta(t as usize),
            });
        }
    }
    Ok(places)
}

/// `Send::free_mask_entries`.
pub fn free_mask_entries(mask_rows: u64, ell_zk: u64, answers: u32) -> u64 {
    if mask_rows == 0 || ell_zk < answers as u64 {
        return 0;
    }
    mask_rows * (ell_zk - answers as u64) + (mask_rows - 1)
}

/// `Send::front`: fixes the cube's bits above the table's.
fn front(z: &[E], c: &SampleCube, table_bits: u32, mask: bool) -> E {
    if !(c.has_main && c.has_mask) {
        return E::ONE;
    }
    let top = c.bits as usize - 1;
    let mut f = if mask { z[top] } else { E::ONE - z[top] };
    for &zt in &z[table_bits as usize..top] {
        f *= E::ONE - zt;
    }
    f
}

/// `Send::form`: o's sample claim for answer `answer` (target left 0).
pub fn form(
    st: &Statement,
    o: OracleId,
    seed: &SampleSeed,
    answer: u32,
) -> Result<Row, &'static str> {
    let s = &st.oracle(o).shape;
    let c = cube(st.codes(), s);
    if (seed.z.len() as u64) < c.bits as u64 {
        return Err("send: the seed is too short");
    }
    if seed.beta == E::ZERO {
        return Err("send: beta is 0");
    }
    let z = &seed.z;
    let mut row = Row::new("sample", RowKind::Sample);
    let on_main = c
        .has_main
        .then(|| Tensor::eq(&z[..c.main_bits as usize], front(z, &c, c.main_bits, false)));
    let on_mask = c
        .has_mask
        .then(|| Tensor::eq(&z[..c.mask_bits as usize], front(z, &c, c.mask_bits, true)));
    for p in pad(st.codes(), s)? {
        let v = match p.part {
            Part::Main => on_main.as_ref(),
            Part::Mask => on_mask.as_ref(),
        }
        .expect("the pad lies in a table the message has");
        let under_z = v.at(p.index);
        let own = if p.answer == answer {
            seed.beta * p.basis
        } else {
            E::ZERO
        };
        row.add_unit(o, p.part, p.index, own - under_z);
    }
    if let Some(v) = on_main {
        row.add(o, Part::Main, v);
    }
    if let Some(v) = on_mask {
        row.add(o, Part::Mask, v);
    }
    Ok(row)
}

/// `Send::verify` after the draws: the sample claims of each sampled oracle message of
/// `ids` (in sending order), with the answers as targets, recorded in the statement.
/// `answers` holds the round's answers by oracle message, then by answer number.
pub fn admit_all(
    st: &mut Statement,
    ids: &[OracleId],
    seeds: &[SampleSeed],
    answers: &[E],
) -> Result<(), &'static str> {
    let todo: Vec<OracleId> = ids
        .iter()
        .copied()
        .filter(|&o| st.oracle(o).shape.answers > 0)
        .collect();
    if todo.is_empty() {
        return Err("send: nothing to sample");
    }
    if todo.windows(2).any(|w| w[0] >= w[1]) {
        return Err("send: oracle messages come in the order of sending");
    }
    let mut next = answers.iter();
    for o in todo {
        let mut rows = Vec::new();
        for i in 0..st.oracle(o).shape.answers {
            let seed = seeds
                .get(i as usize)
                .ok_or("send: no seed for this answer")?;
            let mut row = form(st, o, seed, i)?;
            row.target = *next.next().ok_or("send: an answer is missing")?;
            rows.push(row);
        }
        let places = pad(st.codes(), &st.oracle(o).shape)?
            .into_iter()
            .map(|p| (p.part, p.index))
            .collect();
        st.sampled(o, rows, places)?;
    }
    if next.next().is_some() {
        return Err("send: more answers than sampled entries");
    }
    Ok(())
}

/// The seeds' dimension and count of a round sampling `shapes` (`Send::draw`).
pub fn seed_shape(codes: &Codes, shapes: &[OracleShape]) -> (u32, u32) {
    let sampled = shapes.iter().filter(|s| s.answers > 0);
    let bits = sampled
        .clone()
        .map(|s| cube(codes, s).bits)
        .max()
        .unwrap_or(0);
    let answers = sampled.map(|s| s.answers).max().unwrap_or(0);
    (bits, answers)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::code::Code;
    use flashprove_field::Fp;

    fn e(a: u64, b: u64, c: u64) -> E {
        E([
            Fp::from_canonical(a).unwrap(),
            Fp::from_canonical(b).unwrap(),
            Fp::from_canonical(c).unwrap(),
        ])
    }

    /// The form, entry by entry, against its definition (send_form_test.cpp's statement).
    #[test]
    fn form_is_eq_outside_the_pads_and_beta_basis_on_its_pad() {
        let codes = Codes {
            base: vec![Code {
                log_n: 6,
                ell: 8,
                r: 2,
            }],
            mask: vec![Code {
                log_n: 4,
                ell: 4,
                r: 1,
            }],
        };
        for (main_rows, main_deg, mask_rows) in [(3, 1, 2), (3, 1, 0), (2, 3, 0), (0, 1, 3)] {
            let shape = OracleShape {
                code: (main_rows > 0).then_some(0),
                main_rows,
                main_deg,
                mask_rows,
                mask_code: (mask_rows > 0).then_some(0),
                answers: 2,
            };
            let mut st = Statement::new(codes.clone());
            let o = st.sent(shape).unwrap();
            let c = cube(&codes, &shape);
            let z: Vec<E> = (0..c.bits as u64).map(|i| e(i + 2, 3 * i + 1, i)).collect();
            let seed = SampleSeed {
                z: z.clone(),
                beta: e(5, 1, 7),
            };
            let pads = pad(&codes, &shape).unwrap();
            for answer in 0..2 {
                let row = form(&st, o, &seed, answer).unwrap();
                for (part, has, tbits) in [
                    (Part::Main, c.has_main, c.main_bits),
                    (Part::Mask, c.has_mask, c.mask_bits),
                ] {
                    if !has {
                        continue;
                    }
                    for j in 0..1_u64 << tbits {
                        // The cube point: the table's bits, then 0s, then the part bit on top.
                        let mut point = j;
                        if c.has_main && c.has_mask && part == Part::Mask {
                            point |= 1 << (c.bits - 1);
                        }
                        let want = match pads.iter().find(|p| p.part == part && p.index == j) {
                            Some(p) if p.answer == answer => seed.beta * p.basis,
                            Some(_) => E::ZERO,
                            None => crate::ext::eq_index(point, &z, c.bits),
                        };
                        assert_eq!(row.coefficient(o, part, j), want, "{shape:?} {part:?} {j}");
                    }
                }
            }
        }
    }
}
