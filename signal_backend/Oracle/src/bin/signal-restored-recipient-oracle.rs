//! PUBLIC serialized-SessionRecord receiver fixtures. No handcrafted chain state.
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
  let identity=raw(v,"identity_key_pair");assert_eq!(identity.len(),65);
  let private=PrivateKey::deserialize(&identity[..32]).unwrap();
  assert_eq!(private.public_key().unwrap().serialize().as_ref(),&identity[32..]);
  let identity=IdentityKeyPair::new(IdentityKey::new(private.public_key().unwrap()),private);
  let record=raw(v,"session_record");let parsed=SessionRecord::deserialize(&record).unwrap();
  assert_eq!(parsed.serialize().unwrap(),record);
  let structure=storage::RecordStructure::decode(record.as_slice()).unwrap();
  assert_eq!(structure.current_session.as_ref().unwrap().local_identity_public,identity.public_key().serialize().as_ref());
  let remote=ProtocolAddress::new(v["sender_uuid"].as_str().unwrap().into(),v["sender_device"].as_u64().unwrap_or(1).try_into().map(|d|libsignal_core::DeviceId::new(d).unwrap()).unwrap());
  let local=ProtocolAddress::new(v["recipient_uuid"].as_str().unwrap().into(),v["recipient_device"].as_u64().unwrap_or(1).try_into().map(|d|libsignal_core::DeviceId::new(d).unwrap()).unwrap());
  let mut sessions=InMemSessionStore::new();sessions.store_session(&remote,&parsed).await.unwrap();
  Self{sessions,identities:InMemIdentityKeyStore::new(identity,v["registration_id"].as_u64().unwrap_or(2).try_into().unwrap()),remote,local}
 }

 async fn receive(&mut self,v:&Value)->Value{
  let wire=raw(v,"wire");let Ok(message)=SignalMessage::try_from(wire.as_slice())else{return json!({"accepted":false,"stage":"signal_parse"})};
  let before=self.sessions.load_session(&self.remote).await.unwrap().unwrap().serialize().unwrap();
  let plain=match message_decrypt_signal(&message,&self.remote,&self.local,&mut self.sessions,&mut self.identities,&mut rand::rng()).await{
   Ok(p)=>p,Err(error)=>{assert_eq!(self.sessions.load_session(&self.remote).await.unwrap().unwrap().serialize().unwrap(),before);return json!({"accepted":false,"error":if matches!(error,libsignal_protocol::SignalProtocolError::DuplicatedMessage(..)){"duplicate"}else{"session_decrypt"},"state_preserved":true})}};
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
