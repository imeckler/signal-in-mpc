//! NEW PUBLIC disposable bootstrap reference + actual fresh recipient IPC.
//! No SPQR/session record edits or selected-state override. Rust sender exists
//! ONLY in reference mode; MPC interoperability mode accepts computed wire.
use std::io::{self,BufRead};
use libsignal_protocol::*;
use rand::{SeedableRng,rngs::StdRng};
use serde_json::{Value,json};
use prost::Message;
#[allow(dead_code)]mod service {include!(concat!(env!("OUT_DIR"),"/signalservice.rs"));}
#[derive(Clone,PartialEq,Message)]
struct DataMessage {
 #[prost(string,optional,tag="1")]body:Option<String>,
 #[prost(bytes="vec",optional,tag="6")]profile_key:Option<Vec<u8>>,
 #[prost(uint64,optional,tag="7")]timestamp:Option<u64>,
}
fn hex(x:&[u8])->String{x.iter().map(|b|format!("{b:02x}")).collect()}
fn raw(v:&Value,k:&str)->Vec<u8>{let s=v[k].as_str().unwrap();assert_eq!(s.len()%2,0);(0..s.len()).step_by(2).map(|i|u8::from_str_radix(&s[i..i+2],16).unwrap()).collect()}
struct Peer{
 alice:IdentityKeyPair,bob:IdentityKeyPair,bundle:PreKeyBundle,
 alice_address:ProtocolAddress,bob_address:ProtocolAddress,
 sessions:InMemSessionStore,identities:InMemIdentityKeyStore,
 prekeys:InMemPreKeyStore,signed:InMemSignedPreKeyStore,kyber:InMemKyberPreKeyStore,
 fixture:Value,rng:StdRng,
}
impl Peer{
 async fn new(seed:u64)->Self{
  let mut rng=StdRng::seed_from_u64(seed);let alice=IdentityKeyPair::generate(&mut rng);let bob=IdentityKeyPair::generate(&mut rng);
  let one=KeyPair::generate(&mut rng);let signed_pair=KeyPair::generate(&mut rng);let kem_pair=kem::KeyPair::generate(kem::KeyType::Kyber1024,&mut rng);
  let signed_sig=bob.private_key().calculate_signature(&signed_pair.public_key.serialize(),&mut rng).unwrap();
  let kem_sig=bob.private_key().calculate_signature(&kem_pair.public_key.serialize(),&mut rng).unwrap();
  let bundle:PreKeyBundle=PreKeyBundleContent{registration_id:Some(2),device_id:Some(1u32.try_into().unwrap()),pre_key_id:Some(1u32.into()),pre_key_public:Some(one.public_key),signed_pre_key_id:Some(17u32.into()),signed_pre_key_public:Some(signed_pair.public_key),signed_pre_key_signature:Some(signed_sig.to_vec()),identity_key:Some(*bob.identity_key()),kyber_pre_key_id:Some(23u32.into()),kyber_pre_key_public:Some(kem_pair.public_key.clone()),kyber_pre_key_signature:Some(kem_sig.to_vec())}.try_into().unwrap();
  let alice_address=ProtocolAddress::new("a2000000-0000-4000-8000-000000000001".into(),1u32.try_into().unwrap());let bob_address=ProtocolAddress::new("b2000000-0000-4000-8000-000000000002".into(),1u32.try_into().unwrap());
  let mut prekeys=InMemPreKeyStore::new();prekeys.save_pre_key(1u32.into(),&PreKeyRecord::new(1u32.into(),&one)).await.unwrap();
  let time=Timestamp::from_epoch_millis(1900000000000);let mut signed=InMemSignedPreKeyStore::new();signed.save_signed_pre_key(17u32.into(),&SignedPreKeyRecord::new(17u32.into(),time,&signed_pair,&signed_sig)).await.unwrap();
  let mut kyber=InMemKyberPreKeyStore::new();kyber.save_kyber_pre_key(23u32.into(),&KyberPreKeyRecord::new(23u32.into(),time,&kem_pair,&kem_sig)).await.unwrap();
  let mut identities=InMemIdentityKeyStore::new(bob.clone(),2);identities.save_identity(&alice_address,alice.identity_key()).await.unwrap();
  let fixture=json!({"alice_private":hex(&alice.private_key().serialize()),"alice_identity":hex(&alice.public_key().serialize()),"bob_identity":hex(&bob.public_key().serialize()),"signed_prekey":hex(&signed_pair.public_key.serialize()),"signed_signature":hex(&signed_sig),"one_time_prekey":hex(&one.public_key.serialize()),"kyber_prekey":hex(&kem_pair.public_key.serialize()),"kyber_signature":hex(&kem_sig),"registration_id":2,"device_id":1,"one_time_id":1,"signed_id":17,"kyber_id":23,"trust":"explicit fixture trusted identity, not network authorization","phase_override":false});
  Self{alice,bob,bundle,alice_address,bob_address,sessions:InMemSessionStore::new(),identities,prekeys,signed,kyber,fixture,rng}
 }
 async fn check(&mut self,wire:&[u8])->Value{
  let before=self.sessions.load_session(&self.alice_address).await.unwrap().map(|r|r.serialize().unwrap());
  let pre_before=self.prekeys.get_pre_key(1u32.into()).await.is_ok();let trust_before=self.identities.get_identity(&self.alice_address).await.unwrap();
  let message=match PreKeySignalMessage::try_from(wire){Ok(m)=>m,Err(_)=>return json!({"accepted":false,"error":"decode","session_record_preserved":true})};
  match message_decrypt_prekey(&message,&self.alice_address,&self.bob_address,&mut self.sessions,&mut self.identities,&mut self.prekeys,&self.signed,&mut self.kyber,&mut self.rng).await{
   Ok(result)=>json!({"accepted":true,"plaintext":hex(&result.plaintext),"one_time_consumed":self.prekeys.get_pre_key(1u32.into()).await.is_err(),"sender_identity_matches":result.sender_identity_key==*self.alice.identity_key(),"session_record":hex(&self.sessions.load_session(&self.alice_address).await.unwrap().unwrap().serialize().unwrap())}),
   Err(error)=>{let after=self.sessions.load_session(&self.alice_address).await.unwrap().map(|r|r.serialize().unwrap());let category=if matches!(error,SignalProtocolError::DuplicatedMessage(_, _)){"duplicate"}else{"rejected"};json!({"accepted":false,"error":category,"session_record_preserved":before==after,"one_time_presence_preserved":pre_before==self.prekeys.get_pre_key(1u32.into()).await.is_ok(),"trusted_identity_preserved":trust_before==self.identities.get_identity(&self.alice_address).await.unwrap()})}
  }
 }
 async fn reference(&mut self)->Value{
  let mut sessions=InMemSessionStore::new();let mut identities=InMemIdentityKeyStore::new(self.alice.clone(),1);identities.save_identity(&self.bob_address,self.bob.identity_key()).await.unwrap();
  let mut rng=StdRng::seed_from_u64(0x42534f4f54535452);let time=std::time::SystemTime::UNIX_EPOCH+std::time::Duration::from_secs(1900000000);
  process_prekey_bundle(&self.bob_address,&self.alice_address,&mut sessions,&mut identities,&self.bundle,time,&mut rng).await.unwrap();
  let initial=sessions.load_session(&self.bob_address).await.unwrap().unwrap().serialize().unwrap();let mut rows=vec![];
  for round in 0..2u8{
   let data=DataMessage{body:Some(format!("Actual fresh bootstrap {round}")),timestamp:Some(1900000000000+round as u64),profile_key:None}.encode_to_vec();
   let mut plaintext=service::Content{data_message:Some(data),..Default::default()}.encode_to_vec();assert!(plaintext.len()<80);plaintext.push(128);plaintext.resize(80,0);
   let message=message_encrypt(&plaintext,&self.bob_address,&self.alice_address,&mut sessions,&mut identities,time,&mut rng).await.unwrap();assert_eq!(message.message_type(),CiphertextMessageType::PreKey);
   let wire=message.serialize().to_vec();let parsed=PreKeySignalMessage::try_from(wire.as_slice()).unwrap();let inner=parsed.message().serialized();
   let locations:Vec<_>=wire.windows(inner.len()).enumerate().filter_map(|(at,w)|(w==inner).then_some(at)).collect();assert_eq!(locations.len(),1);
   let mut bad=wire.clone();bad[locations[0]+inner.len()-1]^=1;let rejected=self.check(&bad).await;assert_eq!(rejected["accepted"],false);assert_eq!(rejected["session_record_preserved"],true);assert_eq!(rejected["one_time_presence_preserved"],true);assert_eq!(rejected["trusted_identity_preserved"],true);
   let result=self.check(&wire).await;assert_eq!(result["accepted"],true);assert_eq!(result["plaintext"],hex(&plaintext));assert_eq!(result["one_time_consumed"],true);assert_eq!(result["sender_identity_matches"],true);
   let replay=self.check(&wire).await;assert_eq!(replay["accepted"],false);assert_eq!(replay["error"],"duplicate");assert_eq!(replay["session_record_preserved"],true);assert_eq!(replay["one_time_presence_preserved"],true);assert_eq!(replay["trusted_identity_preserved"],true);
   rows.push(json!({"wire":hex(&wire),"plaintext":hex(&plaintext),"sender_record":hex(&sessions.load_session(&self.bob_address).await.unwrap().unwrap().serialize().unwrap()),"recipient":result,"tamper_rejected_preserved":true,"replay_rejected_preserved":true}));
  }
  json!({"fixture":self.fixture,"initial_sender_record":hex(&initial),"rows":rows,"actual_Rust_reference_only":true,"native_MPC":false,"phase_override":false})
 }
}
fn main(){let rt=tokio::runtime::Builder::new_current_thread().build().unwrap();let mut peer=None;for line in io::stdin().lock().lines(){let value:Value=serde_json::from_str(&line.unwrap()).unwrap();let response=match value["mode"].as_str().unwrap(){"init"=>{let p=rt.block_on(Peer::new(value["seed"].as_u64().unwrap()));let response=p.fixture.clone();peer=Some(p);response},"check"=>rt.block_on(peer.as_mut().unwrap().check(&raw(&value,"wire"))),"reference"=>{let mut p=rt.block_on(Peer::new(value["seed"].as_u64().unwrap()));rt.block_on(p.reference())},_=>panic!("unsupported fixture mode")};println!("{}",response);}}
