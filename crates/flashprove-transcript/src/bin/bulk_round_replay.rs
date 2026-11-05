//! Reassemble the first 512 genuine first-chain Fiat-Shamir messages from
//! *original proof bytes*, using C++-observed read offsets. Not a verifier.
//! In particular, skipped file-only Merkle openings are not checked here.
use flashprove_transcript::first_query::{audit, parameters_digest};
use flashprove_transcript::{first_value, h, run_value, Chain, Digest, RoundKind};
use std::{collections::BTreeMap, env, fs};
const COUNT: usize = 512;

fn from_hex(s: &str) -> Result<Vec<u8>, String> {
    if s.len() % 2 != 0 { return Err("odd hex".into()); }
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i+2],16).map_err(|e|e.to_string())).collect()
}
fn hex(b: &[u8]) -> String { b.iter().map(|x|format!("{x:02x}")).collect() }
fn read_trace(path:&str)->Result<BTreeMap<String,String>,String>{
    if fs::metadata(path).map_err(|e|e.to_string())?.len()>32*1024*1024 {return Err("trace too long".into())}
    let mut t=BTreeMap::new();
    for line in fs::read_to_string(path).map_err(|e|e.to_string())?.lines() {
        let (k,v)=line.split_once('=').ok_or("bad trace line")?;
        if t.insert(k.into(),v.into()).is_some(){return Err(format!("duplicate field {k}"))}
    }
    Ok(t)
}
fn val<'a>(t:&'a BTreeMap<String,String>,k:&str)->Result<&'a str,String>{
    t.get(k).map(String::as_str).ok_or_else(||format!("missing trace field {k}"))
}
fn num(t:&BTreeMap<String,String>,k:&str)->Result<u64,String>{
    val(t,k)?.parse().map_err(|_|format!("bad unsigned integer {k}"))
}
fn decode_digest(t:&BTreeMap<String,String>,name:&str)->Result<Digest,String>{
    from_hex(val(t,name)?)?.try_into().map_err(|_|format!("bad digest {name}"))
}
fn pair(s:&str)->Result<(usize,usize),String>{
    let (left,right)=s.split_once(',').ok_or("bad offset pair")?;
    let a=left.parse::<usize>().map_err(|_|"bad remaining count")?;
    let b=right.parse::<usize>().map_err(|_|"bad span length")?;
    Ok((a,b))
}
fn kind(n:u64)->Result<RoundKind,String>{
    match n {
        1=>Ok(RoundKind::Algebraic),2=>Ok(RoundKind::Epsilon),
        3=>Ok(RoundKind::Seed),4=>Ok(RoundKind::Positions),
        5=>Ok(RoundKind::Bits),6=>Ok(RoundKind::Seal),
        7=>Ok(RoundKind::Empty),_=>Err(format!("bad wire kind {n}"))
    }
}
fn take_span<'a>(proof:&'a[u8],spec:&str,last:&mut usize,gap:&mut usize)->Result<&'a[u8],String>{
    let (remaining,len)=pair(spec)?;
    let end=proof.len().checked_sub(remaining).ok_or("remaining exceeds proof length")?;
    let start=end.checked_sub(len).ok_or("span starts before proof")?;
    if start<*last {return Err(format!("reordered or overlapping read at {start} < {}",*last))}
    *gap=gap.checked_add(start-*last).ok_or("gap counter overflow")?;
    *last=end;
    proof.get(start..end).ok_or_else(||"span exceeds proof".into())
}
fn run(args:&[String])->Result<(),String>{
    if args.len()!=6{return Err("usage: bulk_round_replay TRACE PROOF REQUEST POLICY LAYOUT SCALES".into())}
    let t=read_trace(&args[0])?;
    let proof=fs::read(&args[1]).map_err(|e|e.to_string())?;
    if proof.len()<44||&proof[..8]!=b"CPPFH821"{return Err("bad proof header or missing salt".into())}
    if proof.len()>512*1024*1024{return Err("proof too large".into())}
    let copy=u32::from_le_bytes(proof[8..12].try_into().expect("4 bytes"));
    let request=fs::read(&args[2]).map_err(|e|e.to_string())?;
    let policy=fs::read(&args[3]).map_err(|e|e.to_string())?;
    let layout=fs::read(&args[4]).map_err(|e|e.to_string())?;
    let scales=fs::read(&args[5]).map_err(|e|e.to_string())?;
    let pbytes=from_hex(val(&t,"first_parameters_serialized")?)?;
    let sbytes=from_hex(val(&t,"first_statement_serialized")?)?;
    let plan=audit(&pbytes,&sbytes,[&policy,&layout,&scales],&request,copy).map_err(|e|e.to_string())?;
    if parameters_digest(&pbytes).map_err(|e|e.to_string())?!=decode_digest(&t,"first_parameters")?{
        return Err("parameter digest mismatch".into())
    }
    let salt:Digest=proof[12..44].try_into().expect("32 bytes");
    if salt!=decode_digest(&t,"first_salt")?{return Err("first salt differs from proof".into())}
    let label=0x4652_4d01;
    if num(&t,"first_label")?!=label{return Err("unexpected first-chain label".into())}
    let run=run_value(label,&parameters_digest(&pbytes).map_err(|e|e.to_string())?,&salt).map_err(|e|e.to_string())?;
    let rho0=first_value(label,&parameters_digest(&pbytes).map_err(|e|e.to_string())?,&sbytes,Some(&run)).map_err(|e|e.to_string())?;
    if rho0!=decode_digest(&t,"first_rho0")?{return Err("first-query state mismatch".into())}
    let mut chain=Chain::new(label,rho0).map_err(|e|e.to_string())?;
    let mut cursor=44usize;
    let mut gaps=0usize;
    let mut pindex=0usize;
    let mut pseen=0u64;
    for rno in 1..=COUNT {
        while pindex<plan.rounds.len() && pseen>=plan.rounds[pindex].count {
            pindex+=1;pseen=0;
        }
        let entry=plan.rounds.get(pindex).ok_or("plan ends before replay target")?;
        pseen+=1;
        let key=|suffix:&str|format!("bulk_{rno}_{suffix}");
        if val(&t,&key("name"))?!=entry.name {return Err(format!("plan round {rno}: name mismatch"))}
        if num(&t,&key("work"))?!=entry.work {return Err(format!("plan round {rno}: work mismatch"))}
        let len=usize::try_from(num(&t,&key("size"))?).map_err(|_|"message length overflow")?;
        if u64::try_from(len).map_err(|_|"message length overflow")?!=entry.message_bytes {
            return Err(format!("plan round {rno}: message length mismatch"))
        }
        let mut message=Vec::new();
        for i in 0..100_000usize {
            let label=key(&format!("piece_{i}"));
            let Some(spec)=t.get(&label) else {break};
            let part=take_span(&proof,spec,&mut cursor,&mut gaps)?;
            message.extend_from_slice(part);
            if message.len()>16*1024*1024 {return Err("single message exceeds audit limit".into())}
        }
        if message.len()!=len {return Err(format!("round {rno}: reconstructed {} bytes, expected {len}",message.len()))}
        let digest=h(168,0,0,None,&message,None).map_err(|e|e.to_string())?;
        if hex(&digest)!=val(&t,&key("msg_hash"))? {return Err(format!("round {rno}: actual proof message hash differs"))}
        let work=u8::try_from(entry.work).map_err(|_|"work bits overflow")?;
        let nonce=num(&t,&key("nonce"))?;
        if work!=0 {
            let spec=val(&t,&key("nonce_range"))?;
            let raw=take_span(&proof,spec,&mut cursor,&mut gaps)?;
            if raw.is_empty()||raw.len()>8{return Err(format!("round {rno}: nonce width invalid"))}
            let mut bytes=[0_u8;8];bytes[..raw.len()].copy_from_slice(raw);
            if u64::from_le_bytes(bytes)!=nonce{return Err(format!("round {rno}: nonce mismatch"))}
        } else if nonce!=0 {return Err(format!("round {rno}: unexpected nonce"))}
        let ck=kind(num(&t,&key("kind"))?)?;
        chain.close_round(&message,ck,work,nonce).map_err(|e|format!("round {rno}: {e}"))?;
        if hex(chain.value())!=val(&t,&key("rho"))? {return Err(format!("round {rno}: chain state mismatch"))}
    }
    println!("BULK_FIRST_CHAIN_ROUNDS_OK");
    println!("rounds_replayed={COUNT}");
    println!("file_only_gap_bytes_skipped={gaps}");
    println!("last_observed_proof_offset={cursor}");
    println!("rho_after_last_round={}",hex(chain.value()));
    println!("scope=TRACE_GUIDED_FS_STATES_NOT_MERKLE_CHECKS_OR_PROOF_VERDICT");
    Ok(())
}
fn main(){
    let args:Vec<String>=env::args().skip(1).collect();
    if let Err(e)=run(&args){eprintln!("BULK_ROUND_REPLAY_REJECT: {e}");std::process::exit(1)}
}
