//! Differential oracle for a *real accepted* H821 proof's first round.
//!
//! C++ supplies the first-query public parameter/statement encodings through
//! a diagnostic trace. Rust independently recomputes their hash, decodes the
//! salt and first prover message from the original proof file, executes the
//! first Fiat–Shamir round, and compares sampled challenges.
//!
//! This DOES NOT build a complete first query from config files or verify proofs.

use flashprove_transcript::{first_value, h, run_value, Chain, Digest, RoundKind};
use std::collections::BTreeMap;
use std::env;
use std::fs;

fn read_trace(path: &str) -> Result<BTreeMap<String, String>, String> {
    let metadata = fs::metadata(path).map_err(|e| e.to_string())?;
    if metadata.len() > 32 * 1024 * 1024 {
        return Err("trace too large".into());
    }
    let mut items = BTreeMap::new();
    for line in fs::read_to_string(path).map_err(|e| e.to_string())?.lines() {
        let (key, value) = line.split_once('=').ok_or("malformed trace line")?;
        if items.insert(key.to_string(), value.to_string()).is_some() {
            return Err(format!("duplicate trace key: {key}"));
        }
    }
    Ok(items)
}
fn field<'a>(trace: &'a BTreeMap<String, String>, name: &str) -> Result<&'a str, String> {
    trace.get(name).map(String::as_str).ok_or_else(|| format!("missing {name}"))
}
fn number(trace: &BTreeMap<String, String>, name: &str) -> Result<u64, String> {
    field(trace, name)?.parse::<u64>().map_err(|_| format!("invalid number: {name}"))
}
fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|v| format!("{v:02x}")).collect::<String>()
}
fn unhex(s: &str) -> Result<Vec<u8>, String> {
    if s.len() % 2 != 0 {
        return Err("odd-length hex".into());
    }
    (0..s.len()).step_by(2).map(|i| {
        u8::from_str_radix(&s[i..i + 2], 16).map_err(|e| e.to_string())
    }).collect()
}
fn bytes(trace: &BTreeMap<String, String>, name: &str) -> Result<Vec<u8>, String> {
    unhex(field(trace, name)?)
}
fn digest(trace: &BTreeMap<String, String>, name: &str) -> Result<Digest, String> {
    bytes(trace, name)?.try_into().map_err(|_| format!("{name} must have 32 bytes"))
}
fn same<T: PartialEq + std::fmt::Debug>(label: &str, actual: T, expected: T) -> Result<(), String> {
    if actual != expected {
        Err(format!("{label} differs: Rust={actual:?} C++={expected:?}"))
    } else {
        Ok(())
    }
}
fn parse_kind(kind: u64) -> Result<RoundKind, String> {
    match kind {
        1 => Ok(RoundKind::Algebraic),
        2 => Ok(RoundKind::Epsilon),
        3 => Ok(RoundKind::Seed),
        4 => Ok(RoundKind::Positions),
        5 => Ok(RoundKind::Bits),
        6 => Ok(RoundKind::Seal),
        7 => Ok(RoundKind::Empty),
        _ => Err(format!("invalid round kind {kind}")),
    }
}
fn verify(proof: &[u8], trace: &BTreeMap<String, String>) -> Result<(), String> {
    if proof.len() < 44 || &proof[..8] != b"CPPFH821" {
        return Err("not a complete H821 proof frame and first-chain salt".into());
    }
    const LABEL_FIRST: u64 = 0x4652_4d01;
    same("first-chain label", number(trace, "first_label")?, LABEL_FIRST)?;
    same("first chain must be salted", number(trace, "first_salted")?, 1)?;
    same("first-query record must be empty", number(trace, "first_record_len")?, 0)?;
    let salt = digest(trace, "first_salt")?;
    same("salt read independently from proof[12..44]", &proof[12..44], salt.as_slice())?;

    // The C++ binder supplies the actual parameters and statement encodings.
    // Rust independently hashes them: later work must encode those from the
    // public configuration without using C++ trace bytes.
    let parameters = digest(trace, "first_parameters")?;
    let parameter_bytes = bytes(trace, "first_parameters_serialized")?;
    same(
        "independently hashed first-query parameter serialization",
        h(169, 0, 1, None, &parameter_bytes, None).map_err(|e| e.to_string())?,
        parameters.to_vec(),
    )?;
    let statement = bytes(trace, "first_statement")?;
    same(
        "first-query statement serialization",
        statement.as_slice(),
        bytes(trace, "first_statement_serialized")?.as_slice(),
    )?;
    let run = run_value(LABEL_FIRST, &parameters, &salt).map_err(|e| e.to_string())?;
    let rho0 = first_value(LABEL_FIRST, &parameters, &statement, Some(&run))
        .map_err(|e| e.to_string())?;
    same("first-query digest", rho0, digest(trace, "first_rho0")?)?;

    let kind = parse_kind(number(trace, "first_round_kind")?)?;
    let work_bits = u8::try_from(number(trace, "first_round_work")?)
        .map_err(|_| "work bits overflow")?;
    let nonce = number(trace, "first_round_nonce")?;
    let nonce_bytes = usize::try_from(number(trace, "first_round_nonce_bytes")?)
        .map_err(|_| "nonce width overflow")?;
    if nonce_bytes == 0 || nonce_bytes > 8 {
        return Err("invalid first-round nonce width".into());
    }
    let message_len = usize::try_from(number(trace, "first_round_message_bytes")?)
        .map_err(|_| "message length overflow")?;
    let first = 44_usize;
    let last = first.checked_add(message_len).ok_or("message offset overflow")?;
    let message = proof.get(first..last).ok_or("first message truncated in proof")?;
    same("first message read independently from proof", message, bytes(trace, "first_round_message")?.as_slice())?;
    if message.len() % 8 != 0 {
        return Err("first-round message is not word aligned".into());
    }
    if work_bits == 0 {
        same("nonce of round without work", nonce, 0)?;
    } else {
        let nonce_end = last.checked_add(nonce_bytes).ok_or("nonce offset overflow")?;
        let nonce_field = proof.get(last..nonce_end).ok_or("first-round nonce truncated in proof")?;
        let mut b = [0_u8; 8];
        b[..nonce_bytes].copy_from_slice(nonce_field);
        same("nonce read independently from proof", u64::from_le_bytes(b), nonce)?;
    }

    let mut chain = Chain::new(LABEL_FIRST, rho0).map_err(|e| e.to_string())?;
    let mut draw = chain.close_round(message, kind, work_bits, nonce)
        .map_err(|e| format!("first real round rejected by Rust: {e}"))?;
    same("first-round state digest", *chain.value(), digest(trace, "first_rho1")?)?;

    let mut count = 0;
    for i in 1..=3 {
        let key = format!("first_sample_{i}");
        if let Some(expected) = trace.get(&key) {
            let nonzero = number(trace, &format!("{key}_nonzero"))?;
            if nonzero > 1 {
                return Err(format!("invalid nonzero bit for sample {i}"));
            }
            let x = if nonzero != 0 {
                draw.extension_nonzero().map_err(|e| e.to_string())?
            } else {
                draw.extension().map_err(|e| e.to_string())?
            };
            let actual = x.0.iter().map(|c| c.value().to_string()).collect::<Vec<_>>().join(",");
            same(&key, actual.as_str(), expected.as_str())?;
            count += 1;
        } else {
            break;
        }
    }
    // The first two proof rounds contain no file-only opening or interleaved
    // transcript bytes. Verify that the next C++-absorbed message is exactly
    // the next contiguous proof slice, rather than trusting the trace alone.
    let second_first = last.checked_add(if work_bits > 0 { nonce_bytes } else { 0 })
        .ok_or("second-round start overflow")?;
    let second_len = usize::try_from(number(trace, "second_round_message_bytes")?)
        .map_err(|_| "second message length overflow")?;
    let second_last = second_first.checked_add(second_len).ok_or("second message offset overflow")?;
    let second_message = proof.get(second_first..second_last)
        .ok_or("second message truncated in proof")?;
    same(
        "second prover message read independently from proof",
        second_message,
        bytes(trace, "second_round_message")?.as_slice(),
    )?;
    let second_kind = parse_kind(number(trace, "second_round_kind")?)?;
    let second_work_bits = u8::try_from(number(trace, "second_round_work")?)
        .map_err(|_| "second work bits overflow")?;
    let second_nonce = number(trace, "second_round_nonce")?;
    let second_nonce_bytes = usize::try_from(number(trace, "second_round_nonce_bytes")?)
        .map_err(|_| "second nonce width overflow")?;
    if second_nonce_bytes == 0 || second_nonce_bytes > 8 {
        return Err("invalid second nonce width".into());
    }
    if second_work_bits == 0 {
        same("second round without work has no nonce", second_nonce, 0)?;
    } else {
        let end = second_last.checked_add(second_nonce_bytes).ok_or("second nonce overflow")?;
        let from_proof = proof.get(second_last..end).ok_or("second nonce cut short")?;
        let mut word = [0_u8; 8];
        word[..second_nonce_bytes].copy_from_slice(from_proof);
        same("second nonce read from proof", u64::from_le_bytes(word), second_nonce)?;
    }
    let mut second_draw = chain.close_round(second_message, second_kind, second_work_bits, second_nonce)
        .map_err(|e| format!("second real round rejected by Rust: {e}"))?;
    same("second-round transcript state", *chain.value(), digest(trace, "second_rho2")?)?;
    let mut second_samples = 0;
    for i in 1..=3 {
        let key = format!("second_sample_{i}");
        if let Some(expected) = trace.get(&key) {
            let nonzero = number(trace, &format!("{key}_nonzero"))?;
            if nonzero > 1 {
                return Err(format!("invalid nonzero bit for sample {i}"));
            }
            let x = if nonzero != 0 {
                second_draw.extension_nonzero().map_err(|e| e.to_string())?
            } else {
                second_draw.extension().map_err(|e| e.to_string())?
            };
            let actual = x.0.iter().map(|c| c.value().to_string()).collect::<Vec<_>>().join(",");
            same(&key, actual.as_str(), expected.as_str())?;
            second_samples += 1;
        } else {
            break;
        }
    }
    println!("REAL_FIRST_TWO_ROUNDS_OK");
    println!("proof_leaf_index={}", u32::from_le_bytes(proof[8..12].try_into().expect("four bytes")));
    println!("first_round_name={}", field(trace, "first_round_name")?);
    println!("first_round_message_bytes={message_len}");
    println!("rho0={}", hex(&rho0));
    println!("rho1={}", hex(&digest(trace, "first_rho1")?));
    println!("second_round_name={}", field(trace, "second_round_name")?);
    println!("second_round_message_bytes={second_len}");
    println!("rho2={}", hex(chain.value()));
    println!("sampled_extension_challenges_checked={}", count + second_samples);
    println!("scope=FIRST_TWO_ROUNDS_ONLY_NOT_A_PROOF_VERDICT");
    Ok(())
}

fn main() {
    let args: Vec<String> = env::args().skip(1).collect();
    if args.len() != 2 {
        eprintln!("usage: real_first_round PROOF_FILE CPP_TRACE_FILE");
        std::process::exit(2);
    }
    let result = (|| {
        let metadata = fs::metadata(&args[0]).map_err(|e| e.to_string())?;
        if metadata.len() > 512 * 1024 * 1024 {
            return Err("proof exceeds differential oracle size limit".into());
        }
        let proof = fs::read(&args[0]).map_err(|e| e.to_string())?;
        let trace = read_trace(&args[1])?;
        verify(&proof, &trace)
    })();
    if let Err(why) = result {
        eprintln!("REAL_FIRST_ROUND_MISMATCH: {why}");
        std::process::exit(1);
    }
}
