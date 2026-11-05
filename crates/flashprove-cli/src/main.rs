//! Minimal parsing-only CLI. Never prints YES / ACCEPT.
use flashprove_format::{check_policy_version, parse_next_token, parse_proof, Request};
use std::{env, fs, path::Path};

const MAX_INPUT_BYTES: u64 = 256 * 1024 * 1024;
fn load(path: &str) -> Result<Vec<u8>, String> {
    let metadata = fs::metadata(path).map_err(|e| format!("{path}: {e}"))?;
    if !metadata.is_file() {
        return Err(format!("{path}: not a regular file"));
    }
    if metadata.len() > MAX_INPUT_BYTES {
        return Err(format!("{path}: input exceeds 256 MiB limit"));
    }
    fs::read(Path::new(path)).map_err(|e| format!("{path}: {e}"))
}
fn usage() -> &'static str {
    "Usage:\n  flashprove inspect-proof PROOF_FILE\n  flashprove inspect-request REQUEST_FILE TOKEN_FILE\n  flashprove inspect-bundle POLICY_FILE REQUEST_FILE TOKEN_FILE PROOF_FILE\n  flashprove verify REQUEST_FILE TOKEN_FILE PROOF_FILE\n\nInspection is NOT cryptographic verification.\n"
}
fn execute(args: &[String]) -> Result<(), String> {
    match args {
        [cmd, proof] if cmd == "inspect-proof" => {
            let proof = load(proof)?;
            let envelope = parse_proof(&proof).map_err(|e| e.to_string())?;
            println!(
                "H821 PROOF HEADER: leaf_index={} opaque_body_bytes={}",
                envelope.header.leaf_index,
                envelope.unverified_body.len()
            );
            println!("NOT VERIFIED: plan-dependent proof body has not been parsed");
            Ok(())
        }
        [cmd, request, token] if cmd == "inspect-request" => print_request(request, token),
        [cmd, policy, request, token, proof] if cmd == "inspect-bundle" => {
            check_policy_version(&load(policy)?).map_err(|e| e.to_string())?;
            let p = load(proof)?;
            let env = parse_proof(&p).map_err(|e| e.to_string())?;
            println!("CONFIG: version H821");
            println!(
                "PROOF: leaf_index={} opaque_body_bytes={}",
                env.header.leaf_index,
                env.unverified_body.len()
            );
            print_request(request, token)?;
            println!("NOT VERIFIED: no transcript, commitment, key, or proof checks performed");
            Ok(())
        }
        [cmd, request, token, proof] if cmd == "verify" => {
            let out = flashprove_verifier::verify(&load(proof)?, &load(request)?, &load(token)?);
            Err(format!(
                "NOT CHECKED: {msg}",
                msg = match out {
                    Ok(()) => "unexpected success (bug)".to_string(),
                    Err(err) => err.to_string(),
                }
            ))
        }
        _ => Err(usage().to_string()),
    }
}
fn print_request(request: &str, token: &str) -> Result<(), String> {
    let r = Request::parse(&load(request)?, 1_000_000).map_err(|e| e.to_string())?;
    r.validate_window().map_err(|e| e.to_string())?;
    let y = parse_next_token(&load(token)?).map_err(|e| e.to_string())?;
    r.validate_next_token(y).map_err(|e| e.to_string())?;
    println!(
        "REQUEST: T={} r={} e={} next_token={y}",
        r.tokens.len(),
        r.r,
        r.e
    );
    println!("STRUCTURAL CHECKS ONLY: NOT VERIFIED");
    Ok(())
}
fn main() {
    let args: Vec<String> = env::args().skip(1).collect();
    if let Err(e) = execute(&args) {
        eprintln!("{e}");
        std::process::exit(if args.first().is_some_and(|s| s == "verify") {
            5
        } else {
            2
        });
    }
}
