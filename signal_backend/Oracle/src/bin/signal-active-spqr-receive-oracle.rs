//! PUBLIC disposable selected-epoch fixtures only, actual pinned spqr::recv.
use std::io::{self,BufRead};
use prost::Message;
use serde_json::{Value,json};
#[allow(dead_code)]mod pqr {include!(concat!(env!("OUT_DIR"),"/signal.proto.pq_ratchet.rs"));}
fn raw(v:&Value,k:&str)->Vec<u8>{let s=v[k].as_str().unwrap();assert_eq!(s.len()%2,0);
 (0..s.len()).step_by(2).map(|i|u8::from_str_radix(&s[i..i+2],16).unwrap()).collect()}
fn hex(x:&[u8])->String{x.iter().map(|b|format!("{b:02x}")).collect()}
fn evaluate(v:&Value)->Value{
 let epoch=v["epoch"].as_u64().unwrap();assert!(epoch>0);
 let direction=pqr::chain::epoch::EpochDirection{ctr:v["counter"].as_u64().unwrap().try_into().unwrap(),next:raw(v,"chain"),prev:vec![]};
 let state=pqr::PqRatchetState{version_negotiation:None,
  chain:Some(pqr::Chain{direction:0,current_epoch:epoch-1,send_epoch:epoch-1,
   links:vec![pqr::chain::Epoch{send:Some(direction.clone()),recv:Some(direction)}],next_root:vec![11;32],params:Some(pqr::ChainParams::default())}),
  inner:Some(pqr::pq_ratchet_state::Inner::V1(pqr::V1State{inner_state:Some(
   pqr::v1_state::InnerState::KeysUnsampled(pqr::v1_state::chunked::KeysUnsampled{
    uc:Some(pqr::v1_state::unchunked::KeysUnsampled{epoch,auth:Some(pqr::Authenticator{root_key:vec![9;32],mac_key:vec![10;32]})})}))}))};
 match spqr::recv(&state.encode_to_vec(),&raw(v,"wire")){
  Err(_)=>json!({"accepted":false}),
  Ok(result)=>{
   let after=pqr::PqRatchetState::decode(result.state.as_slice()).unwrap();
   let chain=after.chain.unwrap();let recv=chain.links[0].recv.as_ref().unwrap();
   json!({"accepted":true,"chain":hex(&recv.next),"counter":recv.ctr,"key":hex(&result.key.unwrap())})
  }
 }
}
fn main(){for line in io::stdin().lock().lines(){let v=serde_json::from_str(&line.unwrap()).unwrap();println!("{}",evaluate(&v));}}
