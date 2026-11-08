//! PUBLIC fixtures only: actual pinned SignalMessage parse/MAC API.
use std::io::{self,BufRead};
use serde_json::{Value,json};
use libsignal_protocol::{PublicKey,IdentityKey,SignalMessage,ProtocolAddress};
fn raw(v:&Value,k:&str)->Vec<u8>{let s=v[k].as_str().unwrap();assert_eq!(s.len()%2,0);
 (0..s.len()).step_by(2).map(|i|u8::from_str_radix(&s[i..i+2],16).unwrap()).collect()}
fn identity(v:&Value,k:&str)->IdentityKey{let mut b=vec![5];b.extend(raw(v,k));IdentityKey::new(PublicKey::deserialize(&b).unwrap())}
fn main(){for line in io::stdin().lock().lines(){let v:Value=serde_json::from_str(&line.unwrap()).unwrap();
 let wire=raw(&v,"wire");let sender=ProtocolAddress::new("00112233-4455-6677-8899-aabbccddeeff".into(),1u32.try_into().unwrap());
 let receiver=ProtocolAddress::new("ffeeddcc-bbaa-9988-7766-554433221100".into(),1u32.try_into().unwrap());
 let accepted=SignalMessage::try_from(wire.as_slice()).ok().and_then(|m|m.verify_mac_with_addresses(&sender,&receiver,&identity(&v,"sender"),&identity(&v,"receiver"),&raw(&v,"mac_key")).ok()).unwrap_or(false);
 println!("{}",json!({"accepted":accepted}));}}
