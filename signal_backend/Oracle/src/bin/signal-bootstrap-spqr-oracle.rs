//! PUBLIC actual initial SPQR A2B first/second send; no phase mutation.
use std::io::{self,BufRead};
use prost::Message;
use rand::{RngCore,CryptoRng};
use serde_json::{Value,json};
#[allow(dead_code)]mod pqr {include!(concat!(env!("OUT_DIR"),"/signal.proto.pq_ratchet.rs"));}
fn hex(x:&[u8])->String{x.iter().map(|b|format!("{b:02x}")).collect()}
fn raw(v:&Value,k:&str)->Vec<u8>{let s=v[k].as_str().unwrap();assert_eq!(s.len()%2,0);(0..s.len()).step_by(2).map(|i|u8::from_str_radix(&s[i..i+2],16).unwrap()).collect()}
struct Tape{data:Vec<u8>,offset:usize}
impl RngCore for Tape{
 fn next_u32(&mut self)->u32{let mut b=[0;4];self.fill_bytes(&mut b);u32::from_le_bytes(b)}
 fn next_u64(&mut self)->u64{let mut b=[0;8];self.fill_bytes(&mut b);u64::from_le_bytes(b)}
 fn fill_bytes(&mut self,out:&mut[u8]){let end=self.offset+out.len();assert!(end<=self.data.len(),"unexpected fixture entropy request");out.copy_from_slice(&self.data[self.offset..end]);self.offset=end;}
}
impl CryptoRng for Tape{}
fn snapshot(raw:&[u8])->Value{
 let p=pqr::PqRatchetState::decode(raw).unwrap();let vn=p.version_negotiation.as_ref().unwrap();
 let v=match p.inner.as_ref().unwrap(){pqr::pq_ratchet_state::Inner::V1(v)=>v};
 let sampled=match v.inner_state.as_ref().unwrap(){pqr::v1_state::InnerState::KeysSampled(s)=>s,_=>panic!("unexpected actual phase")};
 let uc=sampled.uc.as_ref().unwrap();let auth=uc.auth.as_ref().unwrap();let encoder=sampled.sending_hdr.as_ref().unwrap();
 let chain=p.chain.as_ref().unwrap();assert_eq!(chain.links.len(),1);let link=&chain.links[0];let send=link.send.as_ref().unwrap();let recv=link.recv.as_ref().unwrap();
 json!({"wire":hex(raw),"phase":"KeysSampled","epoch":uc.epoch,"auth_root":hex(&auth.root_key),"auth_mac":hex(&auth.mac_key),"ek":hex(&uc.ek),"dk":hex(&uc.dk),"polynomial_index":encoder.idx,"polynomial_pts":encoder.pts.iter().map(|x|hex(x)).collect::<Vec<_>>(),"polynomial_polys":encoder.polys.len(),"chain_root":hex(&chain.next_root),"chain_send":hex(&send.next),"chain_counter":send.ctr,"chain_receive":hex(&recv.next),"receive_counter":recv.ctr,"current_epoch":chain.current_epoch,"send_epoch":chain.send_epoch,"negotiation_auth":hex(&vn.auth_key),"direction":vn.direction,"min_version":vn.min_version})
}
fn evaluate(v:&Value)->Value{
 let auth=raw(v,"auth");let seed=raw(v,"seed");assert_eq!(auth.len(),32);assert_eq!(seed.len(),64);
 let initial=spqr::initial_state(spqr::Params{auth_key:&auth,version:spqr::Version::V1,min_version:spqr::Version::V1,direction:spqr::Direction::A2B,chain_params:spqr::ChainParams{max_jump:25_000,max_ooo_keys:2_000}}).unwrap();
 let mut rng=Tape{data:seed,offset:0};let first=spqr::send(&initial,&mut rng).unwrap();assert_eq!(rng.offset,64);
 let mut none=Tape{data:vec![],offset:0};let second=spqr::send(&first.state,&mut none).unwrap();assert_eq!(none.offset,0);
 json!({"initial_state":hex(&initial),"first_state":snapshot(&first.state),"first_message":hex(&first.msg),"first_key":hex(&first.key.unwrap()),"second_state":snapshot(&second.state),"second_message":hex(&second.msg),"second_key":hex(&second.key.unwrap()),"first_entropy_bytes":rng.offset,"second_entropy_bytes":none.offset,"phase_override":false})
}
fn main(){for line in io::stdin().lock().lines(){let value:Value=serde_json::from_str(&line.unwrap()).unwrap();println!("{}",evaluate(&value));}}
