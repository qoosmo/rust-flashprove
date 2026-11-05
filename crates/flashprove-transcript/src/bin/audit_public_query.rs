//! Audit public input bindings on a real proof. C++ still serializes the plan.
use flashprove_transcript::first_query::{audit, parameters_digest};
use std::{collections::BTreeMap, env, fs};
fn from_hex(s:&str)->Result<Vec<u8>,String>{
 if s.len()%2!=0{return Err("odd hex".into())}
 (0..s.len()).step_by(2).map(|i|u8::from_str_radix(&s[i..i+2],16).map_err(|e|e.to_string())).collect()
}
fn trace(path:&str)->Result<BTreeMap<String,String>,String>{
 if fs::metadata(path).map_err(|e|e.to_string())?.len()>32*1024*1024{return Err("trace too long".into())}
 let mut m=BTreeMap::new();
 for line in fs::read_to_string(path).map_err(|e|e.to_string())?.lines(){
  let (k,v)=line.split_once('=').ok_or("bad trace line")?;
  if m.insert(k.into(),v.into()).is_some(){return Err("duplicate trace field".into())}
 }
 Ok(m)
}
fn val<'a>(t:&'a BTreeMap<String,String>,key:&str)->Result<&'a str,String>{
 t.get(key).map(String::as_str).ok_or_else(||format!("missing {key}"))
}
fn num(t:&BTreeMap<String,String>,k:&str)->Result<u64,String>{
 val(t,k)?.parse().map_err(|_|format!("invalid {k}"))
}
fn hex(bytes:&[u8])->String{bytes.iter().map(|x|format!("{x:02x}")).collect()}
fn run(a:&[String])->Result<(),String>{
 if a.len()!=6{return Err("usage: audit_public_query TRACE PROOF REQUEST POLICY LAYOUT SCALES".into())}
 let t=trace(&a[0])?;
 let proof=fs::read(&a[1]).map_err(|e|e.to_string())?;
 if proof.len()<12||&proof[..8]!=b"CPPFH821"{return Err("bad H821 proof".into())}
 let copy=u32::from_le_bytes(proof[8..12].try_into().expect("4 bytes"));
 let request=fs::read(&a[2]).map_err(|e|e.to_string())?;
 let policy=fs::read(&a[3]).map_err(|e|e.to_string())?;
 let layout=fs::read(&a[4]).map_err(|e|e.to_string())?;
 let scales=fs::read(&a[5]).map_err(|e|e.to_string())?;
 let params=from_hex(val(&t,"first_parameters_serialized")?)?;
 let stmt=from_hex(val(&t,"first_statement_serialized")?)?;
 let p=audit(&params,&stmt,[&policy,&layout,&scales],&request,copy).map_err(|e|e.to_string())?;
 let digest=parameters_digest(&params).map_err(|e|e.to_string())?;
 if hex(&digest)!=val(&t,"first_parameters")?{return Err("parameter digest mismatch".into())}
 for (i,prefix,name) in [(0,"first","SEND seed"),(1,"second","SEND answer")] {
  let r=p.rounds.get(i).ok_or("missing plan round")?;
  if r.name!=name||r.name!=val(&t,&format!("{prefix}_round_name"))?
   ||r.message_bytes!=num(&t,&format!("{prefix}_round_message_bytes"))?
   ||r.work!=num(&t,&format!("{prefix}_round_work"))? {
    return Err(format!("{prefix} round differs from public plan"));
  }
 }
 println!("REAL_PUBLIC_QUERY_OK");
 println!("planned_round_entries={}",p.rounds.len());
 let expanded: u64=p.rounds.iter().try_fold(0_u64,|sum,r|sum.checked_add(r.count)).ok_or("round count overflow")?;
 println!("expanded_rounds={expanded}");
 println!("parameter_items={}",p.items.len());
 println!("config_request_copy_bindings=PASS");
 println!("scope=TRACE_SERIALIZED_PLAN_NOT_INDEPENDENT_CONSTRUCTION");
 Ok(())
}
fn main(){
 let a:Vec<String>=env::args().skip(1).collect();
 if let Err(e)=run(&a){eprintln!("REAL_PUBLIC_QUERY_REJECT: {e}");std::process::exit(1)}
}
