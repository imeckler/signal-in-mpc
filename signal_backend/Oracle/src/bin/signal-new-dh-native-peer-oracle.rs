//! PUBLIC disposable fixtures. Actual PQXDH initializes classical DR state;
//! SPQR alone is replaced by a selected established no-chunk phase to isolate
//! the supported active-epoch new-DH receive transition. Not a bootstrap proof.
use std::io::{self,BufRead};
use libsignal_protocol::*;
use prost::Message;
use rand::{SeedableRng,rngs::StdRng};
use serde_json::{Value,json};
#[allow(dead_code)]mod storage {include!(concat!(env!("OUT_DIR"),"/signal.proto.storage.rs"));}
#[allow(dead_code)]mod pqr {include!(concat!(env!("OUT_DIR"),"/signal.proto.pq_ratchet.rs"));}
fn hex(x:&[u8])->String{x.iter().map(|b|format!("{b:02x}")).collect()}
fn raw(v:&Value,k:&str)->Vec<u8>{let s=v[k].as_str().unwrap();(0..s.len()).step_by(2).map(|i|u8::from_str_radix(&s[i..i+2],16).unwrap()).collect()}
fn record(r:&SessionRecord)->storage::RecordStructure{storage::RecordStructure::decode(r.serialize().unwrap().as_slice()).unwrap()}
fn sender(s:&storage::SessionStructure)->Vec<u8>{let c=s.sender_chain.as_ref().unwrap();let k=c.chain_key.as_ref().unwrap();
 [s.root_key.clone(),c.sender_ratchet_key_private.clone(),c.sender_ratchet_key[1..].to_vec(),k.key.clone(),k.index.to_be_bytes().to_vec(),s.previous_counter.to_be_bytes().to_vec()].concat()}
fn receivers(s:&storage::SessionStructure)->Vec<u8>{assert!(s.receiver_chains.len()<=5);let mut out=vec![0;(5-s.receiver_chains.len())*69];
 for c in &s.receiver_chains{let k=c.chain_key.as_ref().unwrap();assert!(c.message_keys.is_empty());out.push(255);out.extend(&c.sender_ratchet_key[1..]);out.extend(&k.key);out.extend(k.index.to_be_bytes());}out}
fn pqstate(direction:spqr::Direction,send:[u8;32],recv:[u8;32])->Vec<u8>{
 let initial=spqr::initial_state(spqr::Params{auth_key:&[15;32],version:spqr::Version::V1,min_version:spqr::Version::V1,direction,chain_params:spqr::ChainParams::default()}).unwrap();
 let mut state=pqr::PqRatchetState::decode(initial.as_slice()).unwrap();let direction=state.version_negotiation.as_ref().unwrap().direction;state.version_negotiation=None;
 state.chain=Some(pqr::Chain{direction,current_epoch:126,send_epoch:126,next_root:vec![16;32],params:Some(pqr::ChainParams::default()),
 links:vec![pqr::chain::Epoch{send:Some(pqr::chain::epoch::EpochDirection{ctr:126,next:send.to_vec(),prev:vec![]}),recv:Some(pqr::chain::epoch::EpochDirection{ctr:126,next:recv.to_vec(),prev:vec![]})}]});
 match state.inner.as_mut().unwrap(){pqr::pq_ratchet_state::Inner::V1(v)=>match v.inner_state.as_mut().unwrap(){
  pqr::v1_state::InnerState::KeysUnsampled(k)=>k.uc.as_mut().unwrap().epoch=127,
  pqr::v1_state::InnerState::NoHeaderReceived(k)=>k.uc.as_mut().unwrap().epoch=127,
  _=>panic!("unexpected initial phase")}}
 state.encode_to_vec()
}
fn receiving_pq(s:&storage::SessionStructure)->Vec<u8>{let p=pqr::PqRatchetState::decode(s.pq_ratchet_state.as_slice()).unwrap();let chain=p.chain.unwrap();let recv=chain.links[0].recv.as_ref().unwrap();
 [(chain.current_epoch+1).to_be_bytes().to_vec(),recv.next.clone(),recv.ctr.to_be_bytes().to_vec()].concat()}
// Stateful public-fixture peer. Fresh native Bob root/private keys are never inputs.
#[path="../relay.rs"]mod relay;
struct Peer {root:PublicKey,sessions:InMemSessionStore,identities:InMemIdentityKeyStore,alice:ProtocolAddress,bob:ProtocolAddress,rng:StdRng,round:u32}
impl Peer {
 async fn new(v:&Value)->(Self,Value){
 let seed=v["seed"].as_u64().unwrap();let mut rng=StdRng::seed_from_u64(seed);
 let alice_id=IdentityKeyPair::generate(&mut rng);let bob_id=IdentityKeyPair::generate(&mut rng);
 let base=KeyPair::generate(&mut rng);let signed=KeyPair::generate(&mut rng);let kyber=kem::KeyPair::generate(kem::KeyType::Kyber1024,&mut rng);
 let parameters=AliceSignalProtocolParameters::new(alice_id.clone(),base,*bob_id.identity_key(),signed.public_key,signed.public_key,kyber.public_key.clone(),false);
 let alice=initialize_alice_session_record(&parameters,&mut rng).unwrap();let mut alice_pb=record(&alice);
 let ciphertext=alice_pb.current_session.as_ref().unwrap().pending_kyber_pre_key.as_ref().unwrap().ciphertext.clone().into_boxed_slice();
 let bob_params=BobSignalProtocolParameters::new(bob_id.clone(),signed,None,kyber,*alice_id.identity_key(),base.public_key,&ciphertext,false);
 let bob=initialize_bob_session_record(&bob_params,&signed).unwrap();let mut bob_pb=record(&bob);
 // Keep genuine PQXDH/DR roots, chain material and ratchet keys unchanged.
 // Selected established PQR phases/direction chains are disposable fixtures.
 alice_pb.current_session.as_mut().unwrap().pq_ratchet_state=pqstate(spqr::Direction::B2A,[21;32],[22;32]);
 bob_pb.current_session.as_mut().unwrap().pq_ratchet_state=pqstate(spqr::Direction::A2B,[22;32],[21;32]);

 let old=bob_pb.current_session.as_ref().unwrap();
 let state=[sender(old),receivers(old),receiving_pq(old)].concat();assert_eq!(state.len(),525);
 let alice=ProtocolAddress::new("00112233-4455-6677-8899-aabbccddeeff".into(),1u32.try_into().unwrap());
 let bob=ProtocolAddress::new("ffeeddcc-bbaa-9988-7766-554433221100".into(),1u32.try_into().unwrap());
 let mut sessions=InMemSessionStore::new();sessions.store_session(&bob,&SessionRecord::deserialize(&alice_pb.encode_to_vec()).unwrap()).await.unwrap();
 let identities=InMemIdentityKeyStore::new(alice_id.clone(),1);
 // Disposable Bob certificate lets the native service reply without exposing
 // any newly generated native ratchet secret/root. Only the public trust root
 // is returned; the peer retains Alice's own actual SessionRecord.
 let root=KeyPair::generate(&mut rng);let signer=KeyPair::generate(&mut rng);
 let server=ServerCertificate::new(1,signer.public_key,&root.private_key,&mut rng).unwrap();
 let cert=SenderCertificate::new("ffeeddcc-bbaa-9988-7766-554433221100".into(),None,*bob_id.public_key(),
  1u32.try_into().unwrap(),Timestamp::from_epoch_millis(2000000000000),server,&signer.private_key,&mut rng).unwrap();
 assert_eq!(cert.serialized().unwrap().len(),260);
 let out=json!({"initial_state":hex(&state),"remote_identity":hex(&alice_id.public_key().serialize()[1..]),
  "local_identity":hex(&bob_id.public_key().serialize()[1..]),"local_identity_fixture_secret":hex(&bob_id.private_key().serialize()),
  "certificate":hex(cert.serialized().unwrap()),"root_public":hex(&root.public_key.serialize()),
  "sending_pq":hex(&[127u64.to_be_bytes().to_vec(),vec![22;32],126u32.to_be_bytes().to_vec()].concat()),
  "selected_established_PQR_phase_override":true,"actual_PQXDH_DR_baseline":true});
 (Self{root:root.public_key,sessions,identities,alice,bob,rng,round:0},out)
 }
 async fn send(&mut self,v:&Value)->Value{
  let plain=raw(v,"plaintext");assert_eq!(plain.len(),80);
  let message=message_encrypt(&plain,&self.bob,&self.alice,&mut self.sessions,&mut self.identities,
   std::time::SystemTime::UNIX_EPOCH+std::time::Duration::from_secs(1900000000),&mut self.rng).await.unwrap();
  assert_eq!(message.message_type(),CiphertextMessageType::Whisper);
  let m=SignalMessage::try_from(message.serialize()).unwrap();assert_eq!(m.counter(),0);
  self.round+=1;
  json!({"wire":hex(message.serialize()),"round":self.round,"counter":m.counter()})
 }
 async fn receive(&mut self,v:&Value)->Value{
  let mut wire=raw(v,"wire");
  if v["mode"]=="frame"{
   let decoded=relay::decode(v);let body=&decoded["body"];
   assert_eq!(decoded["path"],"/v1/messages/00112233-4455-6677-8899-aabbccddeeff?story=false");
   assert_eq!(body["messages"][0]["destinationDeviceId"],1);
   assert_eq!(body["timestamp"].as_u64(),v["timestamp"].as_u64());
   assert_eq!(body["messages"][0]["type"],6);
   let sealed=raw(&decoded,"ciphertext");
   let usmc=sealed_sender_decrypt_to_usmc(&sealed,&self.identities).await.unwrap();
   assert!(usmc.sender().unwrap().validate(&self.root,Timestamp::from_epoch_millis(1900000000000)).unwrap());
   wire=usmc.contents().unwrap().to_vec();
  }
  let Ok(message)=SignalMessage::try_from(wire.as_slice())else{return json!({"accepted":false})};
  match message_decrypt_signal(&message,&self.bob,&self.alice,&mut self.sessions,&mut self.identities,&mut self.rng).await{
   Ok(plain)=>json!({"accepted":true,"plaintext":hex(&plain),"actual_message_decrypt_signal":true}),
   Err(_)=>json!({"accepted":false})
  }
 }
}
fn main(){let rt=tokio::runtime::Builder::new_current_thread().build().unwrap();let mut peer=None;
 for line in io::stdin().lock().lines(){let v:Value=serde_json::from_str(&line.unwrap()).unwrap();
  let out=if v["mode"]=="init"{let(p,out)=rt.block_on(Peer::new(&v));peer=Some(p);out}
  else if v["mode"]=="send"{rt.block_on(peer.as_mut().unwrap().send(&v))}
  else{rt.block_on(peer.as_mut().unwrap().receive(&v))};println!("{out}");}
}
