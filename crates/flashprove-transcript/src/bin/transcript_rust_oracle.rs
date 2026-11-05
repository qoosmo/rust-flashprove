//! Synthetic transcript oracle. Output compared byte-for-byte with C++ Chain.
use flashprove_transcript::{configuration_digest, first_value, run_value, Chain, Digest, RoundKind};

fn digest_hex(value: &Digest) -> String {
    value.iter().map(|b| format!("{b:02x}")).collect()
}
fn ext_text(value: flashprove_field::Ext3) -> String {
    value.0.iter().map(|v| v.value().to_string()).collect::<Vec<_>>().join(",")
}
fn words(numbers: &[u64]) -> Vec<u8> {
    numbers.iter().flat_map(|w| w.to_le_bytes()).collect()
}
fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() != 3 {
        eprintln!("usage: transcript_rust_oracle POLICY LAYOUT SCALES");
        std::process::exit(2);
    }
    let files: Vec<Vec<u8>> = args.iter().map(|p| std::fs::read(p).expect("configuration file")).collect();
    let configuration = configuration_digest(&[
        files[0].as_slice(),
        files[1].as_slice(),
        files[2].as_slice(),
    ]).unwrap();
    println!("configuration={}", digest_hex(&configuration));
    let mut parameters = [0_u8; 32];
    let mut salt = [0_u8; 32];
    for i in 0..32 {
        parameters[i] = ((7 * i + 3) % 251) as u8;
        salt[i] = ((5 * i + 1) % 251) as u8;
    }
    let run = run_value(7, &parameters, &salt).unwrap();
    let rho0 = first_value(7, &parameters, b"rustflashprove-crosslang-v1", Some(&run)).unwrap();
    let mut chain = Chain::new(7, rho0).unwrap();
    println!("rho0={}", digest_hex(chain.value()));

    let mut draw = chain.close_round(&words(&[4, 5, 6, 7, 8, 9]), RoundKind::Algebraic, 0, 0).unwrap();
    println!("rho1={}", digest_hex(chain.value()));
    println!("e1={}", ext_text(draw.extension().unwrap()));
    chain.close_round(&words(&[1, 1, 1]), RoundKind::Empty, 0, 0).unwrap();
    println!("rho2={}", digest_hex(chain.value()));

    let mut draw = chain.close_round(&words(&[11, 22, 33, 44]), RoundKind::Positions, 0, 0).unwrap();
    println!("rho3={}", digest_hex(chain.value()));
    let positions: Vec<String> = (0..5).map(|_| draw.position(10).unwrap().to_string()).collect();
    println!("p3={}", positions.join(","));
    println!("e3={}", ext_text(draw.extension().unwrap()));

    let mut draw = chain.close_round(&[], RoundKind::Seed, 0, 0).unwrap();
    println!("rho4={}", digest_hex(chain.value()));
    println!("z4={}", ext_text(draw.extension().unwrap()));
    println!("beta4={}", ext_text(draw.extension_nonzero().unwrap()));
}
