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
async fn fixture(v:&Value)->Value{
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
 let old=bob_pb.current_session.as_ref().unwrap();let old_sender=sender(old);let old_receivers=receivers(old);let old_pq=receiving_pq(old);
 let alice_address=ProtocolAddress::new("00112233-4455-6677-8899-aabbccddeeff".into(),1u32.try_into().unwrap());
 let bob_address=ProtocolAddress::new("ffeeddcc-bbaa-9988-7766-554433221100".into(),1u32.try_into().unwrap());
 let mut alice_sessions=InMemSessionStore::new();alice_sessions.store_session(&bob_address,&SessionRecord::deserialize(&alice_pb.encode_to_vec()).unwrap()).await.unwrap();
 let mut bob_sessions=InMemSessionStore::new();bob_sessions.store_session(&alice_address,&SessionRecord::deserialize(&bob_pb.encode_to_vec()).unwrap()).await.unwrap();
 let mut alice_identities=InMemIdentityKeyStore::new(alice_id.clone(),1);let mut bob_identities=InMemIdentityKeyStore::new(bob_id.clone(),2);
 let plaintext=raw(v,"plaintext");assert_eq!(plaintext.len(),80);
 let sender_chain_before=alice_pb.current_session.as_ref().unwrap().sender_chain.as_ref().unwrap().chain_key.as_ref().unwrap().key.clone();
 let pqr_probe=spqr::send(&alice_pb.current_session.as_ref().unwrap().pq_ratchet_state,&mut rng.clone()).unwrap();
 let message=message_encrypt(&plaintext,&bob_address,&alice_address,&mut alice_sessions,&mut alice_identities,std::time::SystemTime::UNIX_EPOCH+std::time::Duration::from_secs(1900000000),&mut rng).await.unwrap();
 assert_eq!(message.message_type(),CiphertextMessageType::Whisper);let wire=if v["wire_override"].is_string(){raw(v,"wire_override")}else{message.serialize().to_vec()};let message=SignalMessage::try_from(wire.as_slice()).unwrap();assert_eq!(message.counter(),0);
 assert_eq!(message.pq_ratchet(),pqr_probe.msg.as_slice());
 let mut receive_rng=StdRng::seed_from_u64(seed+1000);let mut cloned=receive_rng.clone();let fresh=KeyPair::generate(&mut cloned);
 let old_private=PrivateKey::deserialize(&old.sender_chain.as_ref().unwrap().sender_ratchet_key_private).unwrap();
 let receiving=old_private.calculate_agreement(message.sender_ratchet_key()).unwrap();let sending=fresh.private_key.calculate_agreement(message.sender_ratchet_key()).unwrap();
 // A failed original MAC must not update the actual retained SessionRecord.
 let before=bob_sessions.load_session(&alice_address).await.unwrap().unwrap().serialize().unwrap();
 let mut tampered=wire.to_vec();*tampered.last_mut().unwrap()^=1;let bad=SignalMessage::try_from(tampered.as_slice()).unwrap();
 assert!(message_decrypt_signal(&bad,&alice_address,&bob_address,&mut bob_sessions,&mut bob_identities,&mut receive_rng.clone()).await.is_err());
 assert_eq!(bob_sessions.load_session(&alice_address).await.unwrap().unwrap().serialize().unwrap(),before);
 let actual=message_decrypt_signal(&message,&alice_address,&bob_address,&mut bob_sessions,&mut bob_identities,&mut receive_rng).await.unwrap();assert_eq!(actual,plaintext);
 let after=bob_sessions.load_session(&alice_address).await.unwrap().unwrap();let after=record(&after);let post=after.current_session.as_ref().unwrap();
 assert_eq!(post.sender_chain.as_ref().unwrap().sender_ratchet_key_private,fresh.private_key.serialize());
 let computed=[fresh.private_key.serialize().to_vec(),fresh.public_key.serialize()[1..].to_vec(),receiving.to_vec(),sending.to_vec()].concat();
 let encoded_wire=[vec![255],(wire.len()as u16).to_be_bytes().to_vec(),wire.to_vec(),vec![0;256-wire.len()]].concat();
 let input=[old_sender,old_receivers,old_pq,alice_id.public_key().serialize()[1..].to_vec(),bob_id.public_key().serialize()[1..].to_vec(),computed,encoded_wire].concat();
 let expected=[vec![255],sender(post),receivers(post),receiving_pq(post),vec![0,80],plaintext].concat();
 json!({"input":hex(&input),"expected":hex(&expected),"wire_bytes":wire.len(),"sender_chain_before":hex(&sender_chain_before),"actual_pq_key":hex(&pqr_probe.key.unwrap()),"actual_PQXDH_initialization":true,"selected_PQR_phase_override":true,"actual_new_DH_message_decrypt":true,"tampered_MAC_preserved_actual_store":true})
}
fn main(){let rt=tokio::runtime::Builder::new_current_thread().build().unwrap();for line in io::stdin().lock().lines(){let v=serde_json::from_str(&line.unwrap()).unwrap();println!("{}",rt.block_on(fixture(&v)));}}
