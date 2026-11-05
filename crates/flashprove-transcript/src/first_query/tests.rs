use super::*;
fn u(v:&mut Vec<u8>,x:u64){v.extend_from_slice(&x.to_le_bytes())}
fn item(v:&mut Vec<u8>,n:&str,b:&[u8]){u(v,n.len() as u64);v.extend_from_slice(n.as_bytes());u(v,b.len() as u64);v.extend_from_slice(b)}
fn make(cfg:&[u8],req:&[u8])->(Vec<u8>,Vec<u8>){
 let mut p=Vec::new();item(&mut p,"the format's version",b"H821\0\0\0\0");
 for x in [2,1,40,8,0,1,0,2]{u(&mut p,x)}
 for (name,msg) in [("SEND seed",64),("SEND answer",96)]{
  u(&mut p,name.len() as u64);p.extend_from_slice(name.as_bytes());
  for x in [1,0,msg,0,0,0,0,0,0,0,0]{u(&mut p,x)}
 }
 item(&mut p,"configuration",cfg);
 let mut s=Vec::new();item(&mut s,"table",&[0;48]);
 item(&mut s,"stored copy",&0_u64.to_le_bytes());item(&mut s,"request",&[0;32]);
 let mut r=Vec::new();u(&mut r,req.len() as u64);r.extend_from_slice(req);
 item(&mut s,"the request file's words",&r);(p,s)
}
#[test] fn plan_and_file_binding(){
 let config=configuration_digest(&[b"policy",b"layout",b"scale"]).unwrap();
 let (p,s)=make(&config,b"req");
 let x=audit(&p,&s,[b"policy",b"layout",b"scale"],b"req",0).unwrap();
 assert_eq!(x.rounds.len(),2);assert_eq!(x.rounds[0].message_bytes,64);
 assert_eq!(x.rounds[1].name,"SEND answer");
 assert_eq!(parameters_digest(&p).unwrap().len(),32);
 assert_eq!(audit(&p,&s,[b"policy",b"layout",b"bad"],b"req",0),Err(QueryError::Configuration));
 assert_eq!(audit(&p,&s,[b"policy",b"layout",b"scale"],b"bad",0),Err(QueryError::Request));
 assert_eq!(audit(&p,&s,[b"policy",b"layout",b"scale"],b"req",1),Err(QueryError::Copy));
}
#[test] fn reject_short_and_trailing(){
 let (p,s)=make(&[7;32],b"req");
 for i in 0..p.len(){assert!(parse_parameters(&p[..i]).is_err())}
 for i in 0..s.len(){assert!(parse_statement(&s[..i]).is_err())}
 let mut q=s.clone();q.push(0);assert_eq!(parse_statement(&q),Err(QueryError::Item));
}
