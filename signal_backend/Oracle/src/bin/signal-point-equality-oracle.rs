//! PUBLIC point equality fixtures using the actual pinned PublicKey API.
use libsignal_protocol::PublicKey;
use serde_json::{Value,json};
use std::io::{self,BufRead};
fn raw(v:&Value,k:&str)->Vec<u8>{let s=v[k].as_str().unwrap();assert_eq!(s.len(),64);let mut out=vec![5];out.extend((0..s.len()).step_by(2).map(|i|u8::from_str_radix(&s[i..i+2],16).unwrap()));out}
fn main(){for line in io::stdin().lock().lines(){let v:Value=serde_json::from_str(&line.unwrap()).unwrap();let left=PublicKey::deserialize(&raw(&v,"left")).unwrap();let right=PublicKey::deserialize(&raw(&v,"right")).unwrap();println!("{}",json!({"equal":left==right}));}}
