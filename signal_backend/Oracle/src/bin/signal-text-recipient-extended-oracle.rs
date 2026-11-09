//! PUBLIC DISPOSABLE RECEIVER FIXTURES ONLY. Actual libsignal session receive,
//! not CBC with supplied final keys. Stateful line protocol retains receiver
//! SessionRecord across calls. No network, production keys, or client opens.
use std::io::{self,BufRead};
use serde_json::{Value,json};
use prost::Message;
use libsignal_protocol::{IdentityKeyPair,IdentityKey,PrivateKey,PublicKey,ProtocolAddress,
 InMemIdentityKeyStore,InMemSessionStore,SessionStore,SessionRecord,SignalMessage,message_decrypt_signal};
#[allow(dead_code)]
mod storage {include!(concat!(env!("OUT_DIR"),"/signal.proto.storage.rs"));}
#[allow(dead_code)]
mod pqr {include!(concat!(env!("OUT_DIR"),"/signal.proto.pq_ratchet.rs"));}
mod service {include!(concat!(env!("OUT_DIR"),"/signalservice.rs"));}
// Exact minimal DataMessage fields used by the pinned relay messaging.rs.
// libsignal's actual service.proto treats DataMessage as opaque bytes.
#[derive(Clone,PartialEq,Message)]
struct DataMessage {
 #[prost(string,optional,tag="1")]body:Option<String>,
 #[prost(bytes="vec",optional,tag="6")]profile_key:Option<Vec<u8>>,
 #[prost(uint64,optional,tag="7")]timestamp:Option<u64>,
}
fn raw(v:&Value,k:&str)->Vec<u8>{let s=v[k].as_str().unwrap();assert_eq!(s.len()%2,0);
 (0..s.len()).step_by(2).map(|i|u8::from_str_radix(&s[i..i+2],16).unwrap()).collect()}
fn hex(x:&[u8])->String{x.iter().map(|b|format!("{b:02x}")).collect()}
fn public(raw:&[u8])->Vec<u8>{let mut b=vec![5];b.extend(raw);PublicKey::deserialize(&b).unwrap();b}
fn text(v:&Value)->Value{
 let body=raw(v,"body");let Ok(body)=String::from_utf8(body)else{return json!({"accepted":false})};
 if body.len()>48{return json!({"accepted":false})}
 let timestamp=v["timestamp"].as_u64().unwrap();
 let dm=DataMessage{body:Some(body),timestamp:Some(timestamp),profile_key:None}.encode_to_vec();
 let content=service::Content{data_message:Some(dm),..Default::default()}.encode_to_vec();
 assert!(content.len()<80);let mut padded=content;padded.push(128);padded.resize(80,0);
 json!({"accepted":true,"padded":hex(&padded)})
}
struct Receiver {sessions:InMemSessionStore,identities:InMemIdentityKeyStore,remote:ProtocolAddress,local:ProtocolAddress}
impl Receiver {
 async fn new(v:&Value)->Self{
  // Receiving chain seeds are receiver-owned disposable fixture state. No
  // sender private identity, ephemeral secret, or derived message keys input.
  let initial=raw(v,"receiving_state");assert_eq!(initial.len(),182);
  let epoch=u64::from_be_bytes(initial[109..117].try_into().unwrap());assert!(epoch>0);
  let ctr=u32::from_be_bytes(initial[105..109].try_into().unwrap());
  let auth=pqr::Authenticator{root_key:vec![9;32],mac_key:vec![10;32]};
  let direction=pqr::chain::epoch::EpochDirection{ctr,next:initial[73..105].to_vec(),prev:vec![]};
  let pq=pqr::PqRatchetState{version_negotiation:None,
   chain:Some(pqr::Chain{direction:0,current_epoch:epoch-1,send_epoch:epoch-1,
    links:vec![pqr::chain::Epoch{send:Some(direction.clone()),recv:Some(direction)}],
    next_root:vec![11;32],params:Some(pqr::ChainParams::default())}),
   inner:Some(pqr::pq_ratchet_state::Inner::V1(pqr::V1State{inner_state:Some(
    pqr::v1_state::InnerState::KeysUnsampled(pqr::v1_state::chunked::KeysUnsampled{
     uc:Some(pqr::v1_state::unchunked::KeysUnsampled{epoch,auth:Some(auth)})}))}))};
  let private=PrivateKey::deserialize(&raw(v,"recipient_secret")).unwrap();
  assert_eq!(private.public_key().unwrap().serialize().as_ref(),public(&initial[150..182]));
  let identity=IdentityKeyPair::new(IdentityKey::new(private.public_key().unwrap()),private);
  let keypair=libsignal_protocol::KeyPair::generate(&mut rand::rng());
  let receiver_chain=storage::session_structure::Chain{sender_ratchet_key:public(&initial[9..41]),
   chain_key:Some(storage::session_structure::chain::ChainKey{
    index:u32::from_be_bytes(initial[1..5].try_into().unwrap()),key:initial[41..73].to_vec()}),..Default::default()};
  let session=storage::SessionStructure{session_version:initial[0]as u32,
   local_identity_public:public(&initial[150..182]),remote_identity_public:public(&initial[118..150]),root_key:vec![12;32],
   sender_chain:Some(storage::session_structure::Chain{sender_ratchet_key:keypair.public_key.serialize().to_vec(),
    sender_ratchet_key_private:keypair.private_key.serialize().to_vec(),
    chain_key:Some(storage::session_structure::chain::ChainKey{index:0,key:vec![13;32]}),..Default::default()}),
   receiver_chains:vec![receiver_chain],pq_ratchet_state:pq.encode_to_vec(),..Default::default()};
  let record=storage::RecordStructure{current_session:Some(session),..Default::default()}.encode_to_vec();
  let remote=ProtocolAddress::new("fixture-sender".into(),1u32.try_into().unwrap());
  let local=ProtocolAddress::new("fixture-recipient".into(),1u32.try_into().unwrap());
  let mut sessions=InMemSessionStore::new();sessions.store_session(&remote,&SessionRecord::deserialize(&record).unwrap()).await.unwrap();
  Self{sessions,identities:InMemIdentityKeyStore::new(identity,1),remote,local}
 }
 async fn receive(&mut self,v:&Value)->Value{
  let wire=raw(v,"wire");let Ok(message)=SignalMessage::try_from(wire.as_slice())else{return json!({"accepted":false,"stage":"signal_parse"})};
  let plain=match message_decrypt_signal(&message,&self.remote,&self.local,&mut self.sessions,&mut self.identities,&mut rand::rng()).await{
   Ok(p)=>p,Err(_)=>return json!({"accepted":false,"stage":"session_decrypt"})};
  let Some(end)=plain.iter().rposition(|&b|b!=0)else{return json!({"accepted":false,"stage":"padding"})};
  if plain[end]!=128{return json!({"accepted":false,"stage":"padding"})}
  let Ok(content)=service::Content::decode(&plain[..end])else{return json!({"accepted":false,"stage":"content"})};
  let Some(dm)=content.data_message else{return json!({"accepted":false,"stage":"data_message_absent"})};
  let Ok(data)=DataMessage::decode(dm.as_slice())else{return json!({"accepted":false,"stage":"data_message"})};
  let mut answer=json!({"accepted":true,"body":data.body,"timestamp":data.timestamp,"padded_bytes":plain.len()});
  if v["inspect_counters"].as_bool().unwrap_or(false){
   let record=self.sessions.load_session(&self.remote).await.unwrap().unwrap();let record=storage::RecordStructure::decode(record.serialize().unwrap().as_slice()).unwrap();let state=record.current_session.unwrap();
   let ratchet=message.sender_ratchet_key().serialize();let receiver=state.receiver_chains.iter().find(|c|c.sender_ratchet_key==ratchet.as_ref()).unwrap();
   let pq=pqr::PqRatchetState::decode(state.pq_ratchet_state.as_slice()).unwrap();
   answer["signal_counter"]=json!(message.counter());answer["next_signal_counter"]=json!(receiver.chain_key.as_ref().unwrap().index);
   answer["pq_receive_counter"]=json!(pq.chain.unwrap().links[0].recv.as_ref().unwrap().ctr);
  }answer
 }
}
fn main(){let rt=tokio::runtime::Builder::new_current_thread().build().unwrap();let mut receivers=std::collections::BTreeMap::new();
 for line in io::stdin().lock().lines(){let v:Value=serde_json::from_str(&line.unwrap()).unwrap();let out=if v["mode"]=="text"{text(&v)}
 else if v["mode"]=="init"{receivers.insert(v["slot"].as_u64().unwrap_or(0),rt.block_on(Receiver::new(&v)));json!({"initialized":true})}
 else{rt.block_on(receivers.get_mut(&v["slot"].as_u64().unwrap_or(0)).unwrap().receive(&v))};println!("{out}");}
}
