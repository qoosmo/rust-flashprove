//! Which tree holds each oracle message, and where its symbols are in a leaf
//! (`lay_trees`, `TreeBook::enter`, `TreeBook::sort_out` in `blocks/iop/context.h`).
//!
//! In one prover message, oracle messages with main rows share a tree when they have the
//! same leaf class and the same code length; mask-only messages then join a tree of their
//! leaf class (any length), or open their own. Trees are numbered in order of creation
//! within a chain; a tree's parts are in sending order. A leaf holds the main symbols of all
//! parts, then the mask symbols of all parts.

use crate::code::Codes;
use crate::relation::{OracleId, Statement, StatementError};
use crate::shapes::{OracleShape, E_DEGREE};

/// `OracleNotice`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OracleNotice {
    pub shape: OracleShape,
    pub leaf_class: u32,
}

/// One tree's shape (`OracleTreeShape` without salt and digests) and its parts.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Tree {
    pub log_n: u32,
    pub log_n_zk: u32,
    pub main_symbols: Vec<u64>,
    pub mask_symbols: Vec<u64>,
    pub parts: Vec<OracleId>,
}
impl Tree {
    pub fn main_width(&self) -> u64 {
        self.main_symbols.iter().sum()
    }
    pub fn mask_width(&self) -> u64 {
        self.mask_symbols.iter().sum()
    }
}

/// Where an oracle message's symbols are: its tree, and the offsets (in F symbols) of its
/// main and mask symbols in a leaf.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Place {
    pub tree: u32,
    pub part: u32,
    pub main_at: u64,
    pub mask_at: u64,
}

/// `TreeBook` (verifier side, one chain).
#[derive(Debug, Clone, Default)]
pub struct TreeBook {
    trees: Vec<Tree>,
    place: Vec<(u32, u32)>,
    first_oracle: OracleId,
}
impl TreeBook {
    /// A book whose first oracle message will have id `first_oracle` in the statement.
    pub fn new(first_oracle: OracleId) -> Self {
        Self {
            trees: Vec::new(),
            place: Vec::new(),
            first_oracle,
        }
    }
    pub fn tree(&self, t: u32) -> &Tree {
        &self.trees[t as usize]
    }
    pub fn trees(&self) -> usize {
        self.trees.len()
    }
    /// `TreeBook::enter`: lays the message's oracle messages into new trees and records them
    /// in the statement (in sending order).
    pub fn enter(
        &mut self,
        st: &mut Statement,
        sent: &[OracleNotice],
    ) -> Result<Vec<OracleId>, StatementError> {
        let codes: &Codes = st.codes();
        let first = self.trees.len();
        let mut new: Vec<Tree> = Vec::new();
        let mut class: Vec<u32> = Vec::new();
        let mut tree_of = vec![0_usize; sent.len()];
        for mask_only in [false, true] {
            for (i, n) in sent.iter().enumerate() {
                let s = &n.shape;
                if (s.main_rows == 0) != mask_only {
                    continue;
                }
                let log_n = if mask_only {
                    0
                } else {
                    let c = s.code.ok_or("trees: main rows without a code")?;
                    codes
                        .base
                        .get(c as usize)
                        .ok_or("statement: no such base code")?
                        .log_n
                };
                let t = (0..new.len())
                    .find(|&t| class[t] == n.leaf_class && (mask_only || new[t].log_n == log_n));
                let t = match t {
                    Some(t) => t,
                    None => {
                        new.push(Tree {
                            log_n,
                            ..Tree::default()
                        });
                        class.push(n.leaf_class);
                        new.len() - 1
                    }
                };
                tree_of[i] = t;
            }
        }
        let mut part_of = vec![0_u32; sent.len()];
        for (i, n) in sent.iter().enumerate() {
            let s = &n.shape;
            let t = &mut new[tree_of[i]];
            if s.mask_rows > 0 {
                let c = s.mask_code.ok_or("trees: mask rows without a code")?;
                let lz = codes
                    .mask
                    .get(c as usize)
                    .ok_or("statement: no such mask code")?
                    .log_n;
                if !t.mask_symbols.iter().all(|&m| m == 0) && t.log_n_zk != lz {
                    return Err("trees: mask rows of two lengths in one tree");
                }
                t.log_n_zk = lz;
            }
            part_of[i] = t.main_symbols.len() as u32;
            t.main_symbols.push(s.main_rows * s.main_deg);
            t.mask_symbols.push(s.mask_rows * E_DEGREE);
        }
        for t in &mut new {
            if t.main_width() == 0 {
                t.log_n = t.log_n_zk;
            }
            if t.mask_width() > 0 && t.log_n_zk > t.log_n {
                return Err("trees: mask rows longer than the main rows above them");
            }
        }
        self.trees.extend(new);
        let mut ids = Vec::new();
        for (i, n) in sent.iter().enumerate() {
            let o = st.sent(n.shape)?;
            if o != self.first_oracle + self.place.len() as OracleId {
                return Err("trees: every oracle message enters the statement through the book");
            }
            let t = (first + tree_of[i]) as u32;
            self.place.push((t, part_of[i]));
            self.trees[t as usize].parts.push(o);
            ids.push(o);
        }
        Ok(ids)
    }
    /// Where o's symbols are in its tree's leaves.
    pub fn place(&self, o: OracleId) -> Option<Place> {
        let &(tree, part) = self.place.get(o.checked_sub(self.first_oracle)? as usize)?;
        let t = &self.trees[tree as usize];
        let p = part as usize;
        Some(Place {
            tree,
            part,
            main_at: t.main_symbols[..p].iter().sum(),
            mask_at: t.main_width() + t.mask_symbols[..p].iter().sum::<u64>(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::code::Code;

    /// The shared chain's round-2 message: G_u (main rows over E) and test_u's fold mask
    /// (mask only), one leaf class: one tree [G_u | mask], as the schedule's tree 0
    /// (main=54,0 mask=0,3).
    #[test]
    fn a_mask_only_message_rides_in_the_tree_of_its_class() {
        let codes = Codes {
            base: vec![Code {
                log_n: 17,
                ell: 8,
                r: 2,
            }],
            mask: vec![Code {
                log_n: 13,
                ell: 4,
                r: 1,
            }],
        };
        let mut st = Statement::new(codes);
        let mut book = TreeBook::new(0);
        let u = OracleShape {
            code: Some(0),
            main_rows: 18,
            main_deg: 3,
            mask_rows: 0,
            mask_code: None,
            answers: 1,
        };
        let m = OracleShape {
            code: None,
            main_rows: 0,
            main_deg: 1,
            mask_rows: 1,
            mask_code: Some(0),
            answers: 0,
        };
        let ids = book
            .enter(
                &mut st,
                &[
                    OracleNotice {
                        shape: u,
                        leaf_class: 0,
                    },
                    OracleNotice {
                        shape: m,
                        leaf_class: 0,
                    },
                ],
            )
            .unwrap();
        assert_eq!(book.trees(), 1);
        let t = book.tree(0);
        assert_eq!((t.log_n, t.log_n_zk), (17, 13));
        assert_eq!(
            (t.main_symbols.clone(), t.mask_symbols.clone()),
            (vec![54, 0], vec![0, 3])
        );
        assert_eq!(
            book.place(ids[1]).unwrap(),
            Place {
                tree: 0,
                part: 1,
                main_at: 54,
                mask_at: 54
            }
        );
        // Another class: its own tree, numbered next.
        let ids = book
            .enter(
                &mut st,
                &[OracleNotice {
                    shape: m,
                    leaf_class: 1,
                }],
            )
            .unwrap();
        assert_eq!(book.place(ids[0]).unwrap().tree, 1);
        assert_eq!(book.tree(1).log_n, 13);
    }
}
