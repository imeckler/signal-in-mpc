//! Native differential fixtures using unchanged pinned libcrux public APIs.
use std::io::{self,BufRead};
fn hex(x:&[u8])->String{x.iter().map(|b|format!("{b:02x}")).collect()}
fn bytes(s:&str)->Vec<u8>{s.as_bytes().chunks(2).map(|p|u8::from_str_radix(std::str::from_utf8(p).unwrap(),16).unwrap()).collect()}
macro_rules! oracle {($module:ident,$seed:expr,$entropy:expr)=>{{
  use libcrux_ml_kem::$module as kem;
  let (sk,pk)=kem::generate_key_pair($seed).into_parts();
  let(ct,ss)=kem::encapsulate(&pk,$entropy);
  let recovered=kem::decapsulate(&sk,&ct);
  println!("{}|{}|{}|{}|{}",hex(sk.as_ref()),hex(pk.as_ref()),hex(ct.as_ref()),hex(ss.as_ref()),hex(recovered.as_ref()));
}}}
macro_rules! decap {($module:ident,$sk:expr,$ct:expr)=>{{use libcrux_ml_kem::$module as kem;let sk=$sk.as_slice().try_into().unwrap();let ct=$ct.as_slice().try_into().unwrap();println!("{}",hex(kem::decapsulate(&sk,&ct).as_ref()));}}}
fn main(){for line in io::stdin().lock().lines(){let line=line.unwrap();let f:Vec<_>=line.split('|').collect();if let Some(mode)=f[0].strip_prefix("decap-"){let sk=bytes(f[1]);let ct=bytes(f[2]);match mode{"mlkem512"=>decap!(mlkem512,sk,ct),"mlkem768"=>decap!(mlkem768,sk,ct),"mlkem1024"=>decap!(mlkem1024,sk,ct),"kyber1024"=>decap!(kyber1024,sk,ct),_=>panic!("variant")};continue;}let seed:[u8;64]=bytes(f[1]).try_into().unwrap();let entropy:[u8;32]=bytes(f[2]).try_into().unwrap();match f[0]{"mlkem512"=>oracle!(mlkem512,seed,entropy),"mlkem768"=>oracle!(mlkem768,seed,entropy),"mlkem1024"=>oracle!(mlkem1024,seed,entropy),"kyber1024"=>oracle!(kyber1024,seed,entropy),_=>panic!("variant")}}}
