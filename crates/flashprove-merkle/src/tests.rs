use super::testing::{given_vertices, Tree};
use super::*;

fn d(b: u8) -> Digest {
    [b; 32]
}
fn shape(log_n: u32, main: usize) -> OracleTreeShape {
    OracleTreeShape {
        log_n,
        log_n_zk: 0,
        main_symbols: vec![main],
        mask_symbols: vec![0],
        tree_number: 3,
        salt_bytes: 40,
        stored: false,
        run: d(7),
        parameters: d(9),
    }
}
fn column(x: u64, w: usize) -> Vec<Fp> {
    (0..w)
        .map(|j| Fp::from_canonical(x * 1000 + j as u64).unwrap())
        .collect()
}
fn salt(x: u64, s: usize) -> Vec<u8> {
    (0..s)
        .map(|j| (x as u8).wrapping_mul(31).wrapping_add(j as u8))
        .collect()
}
struct Built {
    shape: OracleTreeShape,
    tree: Tree,
}
fn build(s: OracleTreeShape) -> Built {
    let w = s.width().unwrap();
    let leaves = (0..1_u64 << s.log_n)
        .map(|x| leaf_digest(&s, x, &column(x, w), &salt(x, s.salt_bytes)).unwrap())
        .collect();
    let tree = Tree::build(&s.parameters, s.log_n, leaves).unwrap();
    Built { shape: s, tree }
}
fn encode(b: &Built, list: &PositionList) -> Vec<u8> {
    let w = b.shape.width().unwrap();
    let mut out = Vec::new();
    for &x in list.all() {
        for s in column(x, w) {
            out.extend_from_slice(&s.to_le_bytes());
        }
        out.extend_from_slice(&salt(x, b.shape.salt_bytes));
    }
    for g in b.tree.given(b.shape.log_n, list).unwrap() {
        out.extend_from_slice(&g);
    }
    out
}

#[test]
fn r7_9_worked_example() {
    // Depth 3, list 0, 5, 7: given digests (3,1), (3,4), (3,6), (2,1), in this order.
    let l = PositionList::from_draws(vec![7, 0, 5, 5], 3).unwrap();
    assert_eq!(l.all(), &[0, 5, 7]);
    assert_eq!(l.draws(), &[7, 0, 5, 5]);
    assert_eq!(
        given_vertices(3, &l).unwrap(),
        vec![(3, 1), (3, 4), (3, 6), (2, 1)]
    );
    assert_eq!(tree_given_count(3, &l).unwrap(), 4);
}

#[test]
fn given_count_bound_r7_9() {
    // g <= t (a - e - 1) + 2^(e+1) - t for 2^e <= t < 2^(e+1).
    let a = 10;
    for seed in 0..50_u64 {
        let draws: Vec<u64> = (0..(seed % 37 + 1))
            .map(|i| (i * 2654435761 + seed * 97) % (1 << a))
            .collect();
        let l = PositionList::from_draws(draws, a).unwrap();
        let t = l.len() as u64;
        let e = 63 - t.leading_zeros() as u64;
        let bound = t * (a as u64 - e - 1) + (1 << (e + 1)) - t;
        assert!(tree_given_count(a, &l).unwrap() as u64 <= bound);
    }
}

#[test]
fn depth_zero_tree_root_is_leaf() {
    let b = build(shape(0, 5));
    let l = PositionList::from_draws(vec![0], 0).unwrap();
    assert_eq!(tree_given_count(0, &l).unwrap(), 0);
    let bytes = encode(&b, &l);
    let mut s = Session::default();
    receive_opening(&bytes, &b.tree.root(), &b.shape, &l, &mut s).unwrap();
}

#[test]
fn honest_openings_accept_and_consume_exactly() {
    for (log_n, w, draws) in [
        (4, 3, vec![1, 2, 9, 9, 15]),
        (6, 17, vec![0, 63]),
        (5, 1, (0..32).collect()),
    ] {
        let b = build(shape(log_n, w));
        let l = PositionList::from_draws(draws, log_n).unwrap();
        let mut bytes = encode(&b, &l);
        assert_eq!(bytes.len(), opening_bytes(&b.shape, &l).unwrap());
        bytes.extend_from_slice(b"trailing");
        let mut s = Session::default();
        let (_, used) = receive_opening(&bytes, &b.tree.root(), &b.shape, &l, &mut s).unwrap();
        assert_eq!(used, bytes.len() - 8);
    }
}

#[test]
fn every_single_byte_flip_rejects() {
    let b = build(shape(4, 2));
    let l = PositionList::from_draws(vec![3, 4, 10], 4).unwrap();
    let bytes = encode(&b, &l);
    for i in 0..bytes.len() {
        for bit in [0_u8, 7] {
            let mut m = bytes.clone();
            m[i] ^= 1 << bit;
            let mut s = Session::default();
            assert!(
                receive_opening(&m, &b.tree.root(), &b.shape, &l, &mut s).is_err(),
                "flip at {i} bit {bit} accepted"
            );
        }
    }
}

#[test]
fn truncation_and_noncanonical_reject() {
    let b = build(shape(3, 2));
    let l = PositionList::from_draws(vec![1, 6], 3).unwrap();
    let bytes = encode(&b, &l);
    for cut in 0..bytes.len() {
        assert!(matches!(
            read_opening(&bytes[..cut], &b.shape, &l),
            Err(MerkleError::Truncated { .. })
        ));
    }
    let mut m = bytes.clone();
    m[8..16].copy_from_slice(&flashprove_field::MODULUS.to_le_bytes());
    assert!(matches!(
        read_opening(&m, &b.shape, &l),
        Err(MerkleError::NonCanonical {
            column: 0,
            symbol: 1,
            ..
        })
    ));
}

#[test]
fn wrong_context_rejects() {
    let b = build(shape(4, 2));
    let l = PositionList::from_draws(vec![5, 12], 4).unwrap();
    let bytes = encode(&b, &l);
    let root = b.tree.root();
    let mut variants = Vec::new();
    let mut s = b.shape.clone();
    s.tree_number = 4;
    variants.push(s);
    let mut s = b.shape.clone();
    s.run = d(8);
    variants.push(s);
    let mut s = b.shape.clone();
    s.parameters = d(10);
    variants.push(s);
    let mut s = b.shape.clone();
    s.stored = true;
    s.tree_number = 0;
    variants.push(s);
    for s in variants {
        let mut sess = Session::default();
        assert!(receive_opening(&bytes, &root, &s, &l, &mut sess).is_err());
    }
    // Another list of the same size: positions are bound into the leaves.
    let l2 = PositionList::from_draws(vec![5, 13], 4).unwrap();
    let mut sess = Session::default();
    assert!(receive_opening(&bytes, &root, &b.shape, &l2, &mut sess).is_err());
    // Another root.
    let mut sess = Session::default();
    assert_eq!(
        receive_opening(&bytes, &d(1), &b.shape, &l, &mut sess).unwrap_err(),
        MerkleError::WrongRoot
    );
}

#[test]
fn invalid_shapes_and_lists_fail_closed() {
    let mut s = shape(4, 2);
    s.salt_bytes = 44;
    assert!(s.validate().is_err());
    let mut s = shape(4, 2);
    s.run = [0; 32];
    assert!(s.validate().is_err());
    let mut s = shape(4, 0);
    s.mask_symbols = vec![3];
    s.log_n_zk = 3;
    assert!(
        s.validate().is_err(),
        "mask-only tree needs log_n == log_n_zk"
    );
    let mut s = shape(4, 2);
    s.stored = true;
    assert!(s.validate().is_err(), "stored tree has number 0");
    assert!(PositionList::from_draws(vec![], 3).is_err());
    assert!(PositionList::from_draws(vec![8], 3).is_err());
    let l = PositionList::from_draws(vec![1], 3).unwrap();
    assert!(opening_bytes(&shape(4, 2), &l).is_err());
}

#[test]
fn short_lists_follow_r7_15() {
    let l = PositionList::from_draws(vec![9, 1, 14, 6], 4).unwrap();
    let s = l.short_list(3).unwrap();
    assert_eq!(s.all(), &[1, 6]);
    assert_eq!(s.draws(), &[1, 1, 6, 6]);
    assert_eq!(l.for_tree(4).unwrap(), l);
}

#[test]
fn record_detects_clash_and_rolls_back() {
    // Two honest openings of one tree share vertices and agree.
    let b = build(shape(4, 2));
    let root = b.tree.root();
    let l1 = PositionList::from_draws(vec![2, 3], 4).unwrap();
    let l2 = PositionList::from_draws(vec![3, 8], 4).unwrap();
    let mut sess = Session::default();
    receive_opening(&encode(&b, &l1), &root, &b.shape, &l1, &mut sess).unwrap();
    let before = sess.record(&root).vertices();
    receive_opening(&encode(&b, &l2), &root, &b.shape, &l2, &mut sess).unwrap();
    assert!(sess.record(&root).vertices() > before);

    // A forged record value makes an otherwise valid opening clash; a rejected
    // opening leaves the record unchanged.
    let mut tv = TreeValues::default();
    tv.seen.insert((1 << 4) + 2, d(0xaa));
    let snapshot = tv.seen.clone();
    let (o, _) = read_opening(&encode(&b, &l1), &b.shape, &l1).unwrap();
    assert_eq!(
        check_opening(&root, &b.shape, &l1, &o, Some(&mut tv)).unwrap_err(),
        MerkleError::Clash
    );
    assert_eq!(tv.seen, snapshot);
    let mut bad = o.clone();
    bad.salts[0] ^= 1;
    let mut fresh = TreeValues::default();
    assert!(check_opening(&root, &b.shape, &l1, &bad, Some(&mut fresh)).is_err());
    assert_eq!(fresh.vertices(), 0);
}

#[test]
fn leaf_fill_boundary() {
    // (16 + 8W) % 128 + s <= 128 -> no fill; otherwise pad to next 128.
    assert_eq!(leaf_salt_at(1, 40).unwrap(), 24);
    // W = 11: 16 + 88 = 104; 104 + 40 > 128 -> fill to 128.
    assert_eq!(leaf_salt_at(11, 40).unwrap(), 128);
}

#[test]
fn leaf_fill_exact() {
    // W = 9: 16 + 72 = 88; 88 + 40 = 128 fits.
    assert_eq!(leaf_salt_at(9, 40).unwrap(), 88);
    // W = 10: 96 + 40 = 136 > 128 -> fill to 128.
    assert_eq!(leaf_salt_at(10, 40).unwrap(), 128);
    // W = 14: 128 % 128 = 0; 0 + 64 <= 128 -> no fill.
    assert_eq!(leaf_salt_at(14, 64).unwrap(), 128);
}

#[test]
fn mask_columns_split() {
    let mut s = shape(3, 2);
    s.main_symbols = vec![2, 1];
    s.mask_symbols = vec![3, 0];
    s.log_n_zk = 2;
    let b = build(s.clone());
    let l = PositionList::from_draws(vec![1, 5], 3).unwrap();
    let (o, _) = read_opening(&encode(&b, &l), &s, &l).unwrap();
    assert_eq!(o.main_column(1).len(), 3);
    assert_eq!(o.mask_column(1).len(), 3);
    assert_eq!(o.column(1), column(5, 6).as_slice());
}
