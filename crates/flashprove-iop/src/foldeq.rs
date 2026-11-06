//! FOLDEQ (`blocks/iop/foldeq.h`): the fold of the committed table at
//! $\gamma$ and the claims it puts on the folded row $G_u$.
//!
//! The table has $2^v$ rows $T_r$ of a code $C$ (length $2^a$). With
//! $e_r = \mathrm{eq}(r, \gamma)$:
//!
//! * the record's answer $i$, folded: $\sum_r e_r\, y_{r\cdot A + i}$ is the
//!   target of the claim (Rec_i);
//! * at a drawn table position $x$ with opened column $T_\cdot(x) \in F^{2^v}$,
//!   the claim (Col) says $G_u$'s codeword has the value
//!   $\sum_r e_r T_r(x)$ there; its coefficients on $G_u$'s message entry $j$
//!   and tail entry $t$ are the generator row at $x$:
//!   $z_x^{\,r_C + j}$ and $z_x^{\,t}$ ($r_C$ = the code's random entries).
//!
//! This module computes these values; the rows themselves are carried by the
//! statement machinery (later steps).

use crate::code::{factors, Code};
use crate::ext::{eq_table, inner_base, product_index};
use crate::shapes::{FoldeqShape, IndexShape, E_DEGREE};
use crate::ParseError;
use flashprove_field::{Ext3 as E, Fp};

/// `IndexRecord`: the committer's answers, $y[r \cdot A + i]$ by row then answer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IndexRecord {
    pub y: Vec<E>,
}

/// The statement item `table` (`public_bytes(IndexName)`): the commitment as a
/// length-prefixed byte string (a 32-byte root), then the record as a list of E.
/// Checks the record's size against the shape and every element's canonical form.
pub fn parse_table_item(
    item: &[u8],
    shape: &IndexShape,
) -> Result<([u8; 32], IndexRecord), ParseError> {
    let word = |at: usize| -> Result<u64, ParseError> {
        item.get(at..at + 8)
            .map(|b| u64::from_le_bytes(b.try_into().expect("8")))
            .ok_or(ParseError::Short { at })
    };
    if word(0)? != 32 {
        return Err(ParseError::Fault(
            "the table's commitment is not a 32-byte root",
        ));
    }
    let root: [u8; 32] = item
        .get(8..40)
        .ok_or(ParseError::Short { at: 8 })?
        .try_into()
        .expect("32");
    let n = usize::try_from(word(40)?).map_err(|_| ParseError::Overflow("record"))?;
    let want = shape
        .rows()
        .checked_mul(u64::from(shape.answers))
        .ok_or(ParseError::Overflow("record"))?;
    if n as u64 != want {
        return Err(ParseError::Fault("record: not a record of this table"));
    }
    let body = &item[48..];
    if body.len() != n.checked_mul(24).ok_or(ParseError::Overflow("record"))? {
        return Err(ParseError::Trailing {
            at: 48,
            len: item.len(),
        });
    }
    let y = body
        .chunks_exact(24)
        .map(|c| {
            E::from_le_bytes(c)
                .map_err(|_| ParseError::Fault("a record entry is not in canonical form"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok((root, IndexRecord { y }))
}

/// `foldeq_weights`: $e_r = \mathrm{eq}(r, \gamma)$, $r < 2^v$.
pub fn weights(s: &FoldeqShape, gamma: &[E]) -> Vec<E> {
    eq_table(gamma, s.index.v)
}

/// The target of (Rec_i): $\sum_r e_r\, y_{r A + i}$.
pub fn record_target(s: &IndexShape, rec: &IndexRecord, i: u32, eq_gamma: &[E]) -> E {
    let a = s.answers as usize;
    (0..s.rows() as usize).fold(E::ZERO, |acc, r| {
        acc + eq_gamma[r] * rec.y[r * a + i as usize]
    })
}

/// `foldeq_symbol`: the fold's value at a position, $\sum_r e_r T_r(x)$.
pub fn column_symbol(eq_gamma: &[E], column: &[Fp]) -> E {
    inner_base(eq_gamma, column)
}

/// `generator_at`: the coefficient of message entry j and tail entry t in the
/// symbol at x: $\text{message\_scale}\cdot\prod_{i<\log \ell,\, j_i} f_i$ and
/// $\text{tail\_scale}\cdot\prod_{i<\log r,\, t_i} f_i$, with $f_i = z_x^{2^i}$,
/// message_scale $= z_x^{r}$, tail_scale $= 1$.
pub struct GeneratorRow {
    pub f: Vec<Fp>,
    pub message_scale: Fp,
    pub tail_scale: Fp,
    code: Code,
}
impl GeneratorRow {
    pub fn at(code: &Code, x: u64) -> Self {
        let f = factors(code.log_n, x, code.log_dim());
        let message_scale = product_index(&f, code.log_dim(), code.message_at());
        let tail_scale = product_index(&f, code.log_dim(), 0);
        Self {
            f,
            message_scale,
            tail_scale,
            code: *code,
        }
    }
    pub fn message(&self, j: u64) -> Fp {
        self.message_scale * product_index(&self.f, self.code.log_ell(), j)
    }
    pub fn tail(&self, t: u64) -> Fp {
        self.tail_scale * product_index(&self.f, self.code.log_r(), t)
    }
}

/// The values that upstream's FOLDEQ block notes (`foldeq_verify`, notes 0-4),
/// from the fold point and the first drawn column.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FoldeqNotes {
    pub e_0: E,
    pub rec_0_target: E,
    pub col_1_target: E,
    pub col_1_on_u_message_0: E,
    pub col_1_on_u_tail_0: E,
}
pub fn notes(
    s: &FoldeqShape,
    gamma: &[E],
    rec: &IndexRecord,
    first_draw: u64,
    first_column: &[Fp],
) -> FoldeqNotes {
    let eq_gamma = weights(s, gamma);
    let g = GeneratorRow::at(&s.index.code, first_draw);
    FoldeqNotes {
        e_0: eq_gamma[0],
        rec_0_target: record_target(&s.index, rec, 0, &eq_gamma),
        col_1_target: column_symbol(&eq_gamma, first_column),
        col_1_on_u_message_0: E::from_base(g.message(0)),
        col_1_on_u_tail_0: if s.index.code.r > 0 {
            E::from_base(g.tail(0))
        } else {
            E::ZERO
        },
    }
}

/// Pad places of the table's rows (`IndexShape::pad_place`), for the record rows.
pub fn pad_place(s: &IndexShape, answer: u32, t: u64) -> u64 {
    s.plain() + E_DEGREE * u64::from(answer) + t
}
