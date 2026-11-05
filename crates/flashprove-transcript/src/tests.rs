use super::*;

fn unhex(s: &str) -> Vec<u8> {
    assert_eq!(s.len() % 2, 0);
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect()
}
fn digest(s: &str) -> Digest {
    unhex(s).try_into().unwrap()
}
fn pattern(n: usize, slope: usize, offset: usize) -> Vec<u8> {
    (0..n).map(|i| ((slope * i + offset) % 251) as u8).collect()
}
fn words(ws: &[u64]) -> Vec<u8> {
    ws.iter().flat_map(|w| w.to_le_bytes()).collect()
}

#[test]
fn hash_known_answers_from_upstream_format_vectors() {
    assert_eq!(
        h(168, 0, 0, None, b"", None).unwrap(),
        unhex("8313e9c466ac5287097eff32299fb13cd2f38c4149e5c06db3672e05c4c584df")
    );
    assert_eq!(
        h(168, 0, 5, None, &pattern(128, 7, 3), None).unwrap(),
        unhex("4d26351ed3e9aacf02412551771a4182b2dd254e97c59b70b8276663cc4fde1f")
    );
    assert_eq!(
        h(168, 0, (1 << 33) + 5, None, &pattern(129, 7, 3), None).unwrap(),
        unhex("0dcff0ef969a659d79a3810bcab9ef0716b249a3d129f2659ed88ddf3f5d55fb")
    );
    let start: Digest = pattern(32, 7, 3).try_into().unwrap();
    assert_eq!(
        h(166, 0, 0, Some(&start), &pattern(64, 7, 3), None).unwrap(),
        unhex("af2a19aa20cc89e1e740e2ec4d34a275eae7bff385fcfc64e3064ccd7cc1b3f8")
    );
    assert_eq!(
        h(164, 9, 12, Some(&start), &pattern(64, 7, 3), Some((3, 5))).unwrap(),
        unhex("a88e3190297571af06940920681fc835d3703d831b5c10d2c5c98ade7383b486")
    );
    assert_eq!(
        round_call(0, 3, &start, &[], RoundKind::Algebraic, 0, 0, 0).unwrap().to_vec(),
        unhex("7dd1787fe5dee7994c6410b994bcd7aec9789019b120012e63ba79f094be483d62ab614467bab4323df78f9a77004db3462e2a38d4eb8e0d431ae6dc57c997ea")
    );
    assert_eq!(
        round_call(1 << 32, 3, &start, &pattern(8, 7, 3), RoundKind::Positions, 8, 5, 1).unwrap().to_vec(),
        unhex("13aafa2ea680d9959c9f20ff463e4c6883414386b4d969a7aaa55496dbc49bdac42b398b0396076027de5292790cf2bd59b8b55c13ba2c3cb0488b791f0d4a93")
    );
}

#[test]
fn first_query_and_full_six_round_toy_against_upstream() {
    // Upstream format-vectors.txt, field 2.
    let parameters = digest("f540c46adb9f25462db0a42935663304d066b78a92bfc4da9d3faa592ceda8f1");
    let statement = unhex(
        "0a00000000000000746f793a20636c61696d18000000000000000100000000000000020000000000000003000000000000000900000000000000746f793a206e616d650b000000000000000300000000000000616263"
    );
    let salt: Digest = pattern(32, 5, 1).try_into().unwrap();
    let run = run_value(7, &parameters, &salt).unwrap();
    assert_eq!(run, digest("700cd5f8c6809036bab546f63e6fd0de6846695ee9772955436353db91d45986"));
    let rho0 = first_value(7, &parameters, &statement, Some(&run)).unwrap();
    assert_eq!(rho0, digest("9a4c85fc23558196c3ee866b926a660f13af5df9a757f1483fcf0bb70aa3fe72"));
    assert_eq!(
        first_value(7, &parameters, &statement, None).unwrap(),
        digest("8f1d3a0a2a3f69ec890ce893d576a15eb38d2f9f11f497eee333c9eb23247f33")
    );
    let mut chain = Chain::new(7, rho0).unwrap();
    let mut draw = chain.close_round(&words(&[4, 5, 6, 7, 8, 9]), RoundKind::Algebraic, 0, 0).unwrap();
    assert_eq!(*chain.value(), digest("3c98919bc70e2dca17b612fdf29be0f6b6f26efcdc04e845a11038260a5861fd"));
    let x = draw.extension().unwrap();
    assert_eq!(
        [x.0[0].value(), x.0[1].value(), x.0[2].value()],
        [4610700807997304418, 4447928095050642327, 12963931155414147300]
    );

    chain.close_round(&words(&[1, 1, 1]), RoundKind::Empty, 0, 0).unwrap();
    assert_eq!(*chain.value(), digest("ed50d6b77518037aa4dfcfd7bae987e6761391c089e349575d6ccac53aa3556f"));

    let root = pattern(32, 11, 2);
    let before = *chain.value();
    assert!(matches!(
        chain.close_round(&root, RoundKind::Positions, 8, 0),
        Err(TranscriptError::WorkNotSatisfied)
    ));
    assert_eq!(*chain.value(), before);
    let mut draw = chain.close_round(&root, RoundKind::Positions, 8, 116).unwrap();
    assert_eq!(*chain.value(), digest("28d010de3f0b0b8da2ccdd36f9c476eb062e1e416389eb81f6a4eb0c60268495"));
    let positions: Vec<u64> = (0..5).map(|_| draw.position(10).unwrap()).collect();
    assert_eq!(positions, [69, 895, 454, 526, 842]);
    let x = draw.extension().unwrap();
    assert_eq!(
        [x.0[0].value(), x.0[1].value(), x.0[2].value()],
        [1566154797897025065, 5902544055155014206, 6066228902280467927]
    );

    let mut draw = chain.close_round(&[], RoundKind::Seed, 0, 0).unwrap();
    assert_eq!(*chain.value(), digest("ad311297fb7c851c0561be363deb88aede14295352d4fcf8f478ed607c8ca10a"));
    let z0 = draw.extension().unwrap();
    let z1 = draw.extension().unwrap();
    let beta = draw.extension_nonzero().unwrap();
    assert_eq!(
        [z0.0[0].value(), z0.0[1].value(), z0.0[2].value()],
        [10242453029133591669, 14074992841984905743, 12408565391145546959]
    );
    assert_eq!(
        [z1.0[0].value(), z1.0[1].value(), z1.0[2].value()],
        [3606079508961713394, 16625540050041287054, 18228235731105415187]
    );
    assert_eq!(
        [beta.0[0].value(), beta.0[1].value(), beta.0[2].value()],
        [12223257125875722716, 11485735129323258346, 7129091038179324709]
    );

    let mut draw = chain.close_round(&words(&[9, 9, 9]), RoundKind::Bits, 0, 0).unwrap();
    assert_eq!(*chain.value(), digest("1377c2217a2329b555a3bc638f2d842dfd01f57cf089aca2cea169d21e70fead"));
    assert_eq!(
        draw.trits(40).unwrap(),
        vec![
            0, 1, 0, 0, -1, -1, 0, 0, -1, 1, -1, 0, 0, 0, 1, 1,
            0, 0, -1, 1, 1, 0, 1, -1, -1, -1, 1, 0, 1, -1, -1, 0,
            0, 0, 0, 1, 0, -1, 0, 1,
        ]
    );

    let mut draw = chain.close_round(&words(&[77]), RoundKind::Seal, 0, 0).unwrap();
    assert_eq!(*chain.value(), digest("70b365d8f0bda8f239fa4a9417b2ddddf69a25197785dd096c937c5d05064dad"));
    assert_eq!(draw.seal().unwrap(), digest("0b5ec9235d31cb34c68dd2f4f50a59b3b0fd28c246389e8f59cd0350416cfdd6"));
}

#[test]
fn configuration_digest_toy_file_matches_upstream() {
    assert_eq!(
        configuration_digest(&[b"toy\n"]).unwrap(),
        digest("e7b508817ead50bb3f386f68d442b114119e93e8ef2b14a7d70190075348db5f")
    );
    assert_ne!(
        configuration_digest(&[b"toy\n"]).unwrap(),
        configuration_digest(&[b"toy"]).unwrap()
    );
}

#[test]
fn domain_and_work_rejections_are_fail_closed() {
    let rho = [0_u8; 32];
    assert_eq!(h(177, 0, 0, None, b"", None), Err(TranscriptError::InvalidDomain(177)));
    assert_eq!(h(162, 0, 1, None, b"", None), Err(TranscriptError::InvalidHashArguments));
    assert_eq!(h(168, 0, 0, Some(&rho), b"", None), Err(TranscriptError::InvalidHashArguments));
    assert_eq!(h(164, 0, 0, Some(&rho), b"", None), Err(TranscriptError::InvalidShape));
    let mut chain = Chain::new(7, rho).unwrap();
    assert!(matches!(
        chain.close_round(b"bad", RoundKind::Algebraic, 0, 0),
        Err(TranscriptError::MisalignedRoundMessage)
    ));
    assert!(matches!(
        chain.close_round(&[], RoundKind::Empty, 1, 0),
        Err(TranscriptError::InvalidWork(1))
    ));
    assert!(matches!(
        chain.close_round(&[], RoundKind::Algebraic, 0, 1),
        Err(TranscriptError::UnexpectedNonce)
    ));
    assert_eq!(chain.rounds(), 0);
}
