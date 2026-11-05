//! H821 R4.3/R14.3 public first-query parser.
//! Audits C++-serialized inputs against actual files. It does NOT independently
//! construct the full protocol plan from model parameters.
use crate::{configuration_digest, h, Digest};
use core::fmt;
const MAX_PUBLIC: usize = 16*1024*1024;
#[derive(Debug,Clone,PartialEq,Eq)]
pub enum QueryError { Short, Limit, Utf8, Version, Plan, Item, Configuration, Request, Copy, Hash }
impl fmt::Display for QueryError { fn fmt(&self,f:&mut fmt::Formatter<'_>)->fmt::Result { write!(f,"{self:?}") } }
impl std::error::Error for QueryError {}
struct Cursor<'a> { b:&'a [u8], at:usize }
impl<'a> Cursor<'a> {
 fn new(b:&'a [u8])->Result<Self,QueryError> {
  if b.len()>MAX_PUBLIC {return Err(QueryError::Limit)} Ok(Self{b,at:0})
 }
 fn take(&mut self,n:usize)->Result<&'a[u8],QueryError> {
  let end=self.at.checked_add(n).ok_or(QueryError::Limit)?;
  let x=self.b.get(self.at..end).ok_or(QueryError::Short)?;self.at=end;Ok(x)
 }
 fn word(&mut self)->Result<u64,QueryError> { Ok(u64::from_le_bytes(self.take(8)?.try_into().expect("8 bytes"))) }
 fn sized(&mut self,limit:usize)->Result<&'a[u8],QueryError> {
  let n=usize::try_from(self.word()?).map_err(|_|QueryError::Limit)?;
  if n>limit {return Err(QueryError::Limit)} self.take(n)
 }
 fn item(&mut self)->Result<Item,QueryError> {
  let raw=self.sized(512)?;
  let name=std::str::from_utf8(raw).map_err(|_|QueryError::Utf8)?;
  if name.is_empty() || !name.bytes().all(|x| (32..127).contains(&x)) {return Err(QueryError::Item)}
  Ok(Item{name:name.to_string(),value:self.sized(MAX_PUBLIC)?.to_vec()})
 }
 fn done(&self)->bool {self.at==self.b.len()}
}
#[derive(Debug,Clone,PartialEq,Eq)] pub struct Item {pub name:String,pub value:Vec<u8>}
#[derive(Debug,Clone,PartialEq,Eq)]
pub struct Round {
 pub name:String,pub count:u64,pub work:u64,pub message_bytes:u64,
 pub roots:u64,pub answers:u64,pub draw_e:u64,pub nonzero:u64,
 pub positions:u64,pub log_n:u64,pub trits:u64,pub rows:u64
}
#[derive(Debug,Clone,PartialEq,Eq)]
pub struct Parameters {
 pub field:u64,pub hash:u64,pub salt_bytes:u64,pub nonce_bytes:u64,
 pub position_bytes:u64,pub samples:u64,pub saved:u64,
 pub rounds:Vec<Round>,pub items:Vec<Item>
}
pub fn parse_parameters(input:&[u8])->Result<Parameters,QueryError> {
 let mut c=Cursor::new(input)?;
 let version=c.item()?;
 if version.name!="the format's version" || version.value!=b"H821\0\0\0\0" {return Err(QueryError::Version)}
 let field=c.word()?;let hash=c.word()?;let salt_bytes=c.word()?;
 let nonce_bytes=c.word()?;let position_bytes=c.word()?;
 let samples=c.word()?;let saved=c.word()?;
 let n=usize::try_from(c.word()?).map_err(|_|QueryError::Limit)?;
 if field!=2 || hash!=1 || !(40..=64).contains(&salt_bytes)
  || nonce_bytes==0 || nonce_bytes>8 || position_bytes>8 || n==0 || n>200_000 {
   return Err(QueryError::Plan);
 }
 let mut rounds=Vec::with_capacity(n);
 for _ in 0..n {
  let namebytes=c.sized(512)?;
  let name=std::str::from_utf8(namebytes).map_err(|_|QueryError::Utf8)?;
  if name.is_empty() || !name.bytes().all(|x|(32..127).contains(&x)) {return Err(QueryError::Plan)}
  let count=c.word()?;let work=c.word()?;let message_bytes=c.word()?;
  let roots=c.word()?;let answers=c.word()?;let draw_e=c.word()?;
  let nonzero=c.word()?;let positions=c.word()?;let log_n=c.word()?;
  let trits=c.word()?;let rows=c.word()?;
  if count==0 || work>64 || message_bytes>1<<30 || message_bytes%8!=0
   || nonzero>draw_e || (positions>0 && log_n>=64) {return Err(QueryError::Plan)}
  rounds.push(Round{name:name.to_string(),count,work,message_bytes,
   roots,answers,draw_e,nonzero,positions,log_n,trits,rows});
 }
 let mut items=Vec::new();
 while !c.done() {
  if items.len()>=256 {return Err(QueryError::Limit)}
  items.push(c.item()?);
 }
 Ok(Parameters{field,hash,salt_bytes,nonce_bytes,position_bytes,
  samples,saved,rounds,items})
}
pub fn parse_statement(input:&[u8])->Result<Vec<Item>,QueryError> {
 let mut c=Cursor::new(input)?;
 let mut items=Vec::new();
 for name in ["table","stored copy","request","the request file's words"] {
  let item=c.item()?;
  if item.name!=name {return Err(QueryError::Item)}
  items.push(item);
 }
 if !c.done() {return Err(QueryError::Item)}
 Ok(items)
}
/// Check that the hash of the serialized public input is reproducible in Rust.
pub fn parameters_digest(input:&[u8])->Result<Digest,QueryError> {
 h(169,0,1,None,input,None).map_err(|_|QueryError::Hash)?
  .try_into().map_err(|_|QueryError::Hash)
}
/// Audits bindings: one configuration digest; exact copy id and request bytes.
pub fn audit(input:&[u8],statement:&[u8],files:[&[u8];3],
 request:&[u8],copy:u32)->Result<Parameters,QueryError> {
 let parsed=parse_parameters(input)?;
 let config=configuration_digest(&files).map_err(|_|QueryError::Hash)?;
 let config_items:Vec<_>=parsed.items.iter().filter(|i|i.name=="configuration").collect();
 if config_items.len()!=1 {return Err(QueryError::Item)}
 if config_items[0].value.as_slice()!=config {return Err(QueryError::Configuration)}
 let stmt=parse_statement(statement)?;
 if stmt[1].value.len()!=8 || u64::from_le_bytes(stmt[1].value[..8].try_into().expect("8 bytes"))!=u64::from(copy) {
  return Err(QueryError::Copy)
 }
 let mut c=Cursor::new(&stmt[3].value)?;
 if c.sized(MAX_PUBLIC)?!=request || !c.done() {return Err(QueryError::Request)}
 Ok(parsed)
}
#[cfg(test)] mod tests;
