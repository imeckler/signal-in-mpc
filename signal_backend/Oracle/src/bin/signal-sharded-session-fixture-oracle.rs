//! NEW PUBLIC disposable multi-peer/6+message fixtures; no old fixture changes.
//! PUBLIC disposable fixtures. Actual PQXDH initializes classical DR state;
//! SPQR alone is replaced by a selected established no-chunk phase to isolate
//! the supported active-epoch new-DH receive transition. Not a bootstrap proof.
use std::io::{self,BufRead};
#[path="../session_projection.rs"]mod session_projection;
#[path="../session_send_projection.rs"]mod session_send_projection;
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

// PUBLIC disposable whole-store fixture via actual target APIs. The Kyber
// replay set is mirrored from the exact calls below because InMem exposes no
// iterator for its private base_keys_seen map; restore is checked through APIs.
async fn global_stores(alice:&IdentityKeyPair,remote:&IdentityKey,address:&ProtocolAddress,seed:u64,extras:&Value)->Value{
 let mut rng=StdRng::seed_from_u64(seed+8000);
 let mut identities=InMemIdentityKeyStore::new(alice.clone(),1);identities.save_identity(address,remote).await.unwrap();
 let mut peers=vec![(address.clone(),*remote)];
 if let Some(extra)=extras.as_array(){assert!(extra.len()<=3);for peer in extra{
  let other=ProtocolAddress::new(peer["name"].as_str().unwrap().into(),1u32.try_into().unwrap());
  assert!(!peers.iter().any(|(prior,_)|prior==&other));let key=IdentityKey::decode(&raw(peer,"identity")).unwrap();
  identities.save_identity(&other,&key).await.unwrap();peers.push((other,key));
 }}
 let mut pre=InMemPreKeyStore::new();
 for id in [1u32,2u32]{let pair=KeyPair::generate(&mut rng);pre.save_pre_key(id.into(),&PreKeyRecord::new(id.into(),&pair)).await.unwrap();}
 pre.remove_pre_key(1u32.into()).await.unwrap();assert!(pre.get_pre_key(1u32.into()).await.is_err());
 let pair=KeyPair::generate(&mut rng);let signature=alice.private_key().calculate_signature(&pair.public_key.serialize(),&mut rng).unwrap();
 let signed=SignedPreKeyRecord::new(17u32.into(),Timestamp::from_epoch_millis(1900000000000),&pair,&signature);
 let mut signed_store=InMemSignedPreKeyStore::new();signed_store.save_signed_pre_key(17u32.into(),&signed).await.unwrap();
 let kem=kem::KeyPair::generate(kem::KeyType::Kyber1024,&mut rng);let signature=alice.private_key().calculate_signature(&kem.public_key.serialize(),&mut rng).unwrap();
 let kyber=KyberPreKeyRecord::new(23u32.into(),Timestamp::from_epoch_millis(1900000000000),&kem,&signature);
 let mut kyber_store=InMemKyberPreKeyStore::new();kyber_store.save_kyber_pre_key(23u32.into(),&kyber).await.unwrap();
 let seen=[KeyPair::generate(&mut rng).public_key,KeyPair::generate(&mut rng).public_key];
 for key in &seen{kyber_store.mark_kyber_pre_key_used(23u32.into(),17u32.into(),key).await.unwrap();}
 assert!(kyber_store.mark_kyber_pre_key_used(23u32.into(),17u32.into(),&seen[0]).await.is_err());
 let pre_bytes=pre.get_pre_key(2u32.into()).await.unwrap().serialize().unwrap();
 let signed_bytes=signed_store.get_signed_pre_key(17u32.into()).await.unwrap().serialize().unwrap();
 let kyber_bytes=kyber_store.get_kyber_pre_key(23u32.into()).await.unwrap().serialize().unwrap();
 let mut restored_pre=InMemPreKeyStore::new();restored_pre.save_pre_key(2u32.into(),&PreKeyRecord::deserialize(&pre_bytes).unwrap()).await.unwrap();
 assert!(restored_pre.get_pre_key(1u32.into()).await.is_err());assert_eq!(restored_pre.get_pre_key(2u32.into()).await.unwrap().serialize().unwrap(),pre_bytes);
 let mut restored_signed=InMemSignedPreKeyStore::new();restored_signed.save_signed_pre_key(17u32.into(),&SignedPreKeyRecord::deserialize(&signed_bytes).unwrap()).await.unwrap();
 assert_eq!(restored_signed.get_signed_pre_key(17u32.into()).await.unwrap().serialize().unwrap(),signed_bytes);
 let mut restored_kyber=InMemKyberPreKeyStore::new();restored_kyber.save_kyber_pre_key(23u32.into(),&KyberPreKeyRecord::deserialize(&kyber_bytes).unwrap()).await.unwrap();
 for key in &seen{restored_kyber.mark_kyber_pre_key_used(23u32.into(),17u32.into(),key).await.unwrap();}
 assert!(restored_kyber.mark_kyber_pre_key_used(23u32.into(),17u32.into(),&seen[0]).await.is_err());
 assert_eq!(restored_kyber.get_kyber_pre_key(23u32.into()).await.unwrap().serialize().unwrap(),kyber_bytes);
 let trusted=identities.get_identity(address).await.unwrap().unwrap();
 assert!(alice.public_key().verify_signature(&pair.public_key.serialize(),&signed.signature().unwrap()));
 assert!(alice.public_key().verify_signature(&kem.public_key.serialize(),&kyber.signature().unwrap()));
 // Versioned whole registration/prekey/trust/replay content. Count/length
 // encoding is a public-fixture reference; MPC stores it as secret bytes.
 let mut encoded=b"SIGNAL-GLOBAL-STORE-V1/904c8dc".to_vec();
 encoded.extend(1u32.to_be_bytes());
 encoded.extend((peers.len()as u16).to_be_bytes());
 for (peer,key)in &peers{let name=peer.name().as_bytes();encoded.extend((name.len()as u16).to_be_bytes());encoded.extend(name);
 encoded.extend(1u32.to_be_bytes());encoded.extend(key.serialize());}
 for (id,data) in [(2u32,&pre_bytes),(17u32,&signed_bytes),(23u32,&kyber_bytes)]{
  encoded.extend(1u16.to_be_bytes());encoded.extend(id.to_be_bytes());encoded.extend((data.len()as u16).to_be_bytes());encoded.extend(data);
 }
 encoded.extend(1u16.to_be_bytes());encoded.extend(23u32.to_be_bytes());encoded.extend(17u32.to_be_bytes());encoded.extend(2u16.to_be_bytes());
 for key in &seen{encoded.extend(key.serialize());}
 let mut at=b"SIGNAL-GLOBAL-STORE-V1/904c8dc".len();
 fn take<'a>(raw:&'a[u8],at:&mut usize,n:usize)->&'a[u8]{let data=raw.get(*at..*at+n).expect("bounded global store fixture");*at+=n;data}
 fn u16_at(raw:&[u8],at:&mut usize)->u16{u16::from_be_bytes(take(raw,at,2).try_into().unwrap())}
 fn u32_at(raw:&[u8],at:&mut usize)->u32{u32::from_be_bytes(take(raw,at,4).try_into().unwrap())}
 let registration=u32_at(&encoded,&mut at);let mut restored_id=InMemIdentityKeyStore::new(alice.clone(),registration);
 let peer_count=u16_at(&encoded,&mut at)as usize;assert_eq!(peer_count,peers.len());
 for _ in 0..peer_count{let name_len=u16_at(&encoded,&mut at)as usize;let name=std::str::from_utf8(take(&encoded,&mut at,name_len)).unwrap().to_string();
 let device=u32_at(&encoded,&mut at);let restored_address=ProtocolAddress::new(name,device.try_into().unwrap());
 let identity=IdentityKey::decode(take(&encoded,&mut at,33)).unwrap();restored_id.save_identity(&restored_address,&identity).await.unwrap();}
 let mut restored_pre=InMemPreKeyStore::new();let mut restored_signed=InMemSignedPreKeyStore::new();let mut restored_kyber=InMemKyberPreKeyStore::new();
 for kind in 0..3{assert_eq!(u16_at(&encoded,&mut at),1);let id=u32_at(&encoded,&mut at);let n=u16_at(&encoded,&mut at)as usize;let data=take(&encoded,&mut at,n);
  match kind {0=>restored_pre.save_pre_key(id.into(),&PreKeyRecord::deserialize(data).unwrap()).await.unwrap(),1=>restored_signed.save_signed_pre_key(id.into(),&SignedPreKeyRecord::deserialize(data).unwrap()).await.unwrap(),_=>restored_kyber.save_kyber_pre_key(id.into(),&KyberPreKeyRecord::deserialize(data).unwrap()).await.unwrap()}
 }
 assert_eq!(u16_at(&encoded,&mut at),1);let kid=u32_at(&encoded,&mut at);let sid=u32_at(&encoded,&mut at);let n=u16_at(&encoded,&mut at);
 for _ in 0..n{let key=PublicKey::deserialize(take(&encoded,&mut at,33)).unwrap();restored_kyber.mark_kyber_pre_key_used(kid.into(),sid.into(),&key).await.unwrap();}
 assert_eq!(at,encoded.len());assert!(restored_pre.get_pre_key(1u32.into()).await.is_err());
 assert_eq!(restored_pre.get_pre_key(2u32.into()).await.unwrap().serialize().unwrap(),pre_bytes);
 assert_eq!(restored_signed.get_signed_pre_key(17u32.into()).await.unwrap().serialize().unwrap(),signed_bytes);
 assert_eq!(restored_kyber.get_kyber_pre_key(23u32.into()).await.unwrap().serialize().unwrap(),kyber_bytes);
 assert_eq!(restored_id.get_identity(address).await.unwrap().unwrap(),trusted);
 for (peer,key)in &peers{assert_eq!(restored_id.get_identity(peer).await.unwrap().unwrap(),*key);}
 assert!(restored_kyber.mark_kyber_pre_key_used(23u32.into(),17u32.into(),&seen[0]).await.is_err());
 json!({"global_store_v1":hex(&encoded),"actual_whole_global_store_codec_reload":true,"identity_private_public65":hex(&[alice.private_key().serialize().to_vec(),alice.public_key().serialize().to_vec()].concat()),
  "trusted_peers":peers.iter().map(|(peer,key)|json!({"name":peer.name(),"device":1,"identity":hex(&key.serialize())})).collect::<Vec<_>>(),"registration_id":identities.get_local_registration_id().await.unwrap(),"trusted_identity":hex(&trusted.serialize()),
  "prekeys":[{"id":2,"record":hex(&pre_bytes)}],"consumed_prekey_ids":[1],"signed_prekeys":[{"id":17,"record":hex(&signed_bytes)}],
  "kyber_prekeys":[{"id":23,"record":hex(&kyber_bytes)}],"kyber_base_keys_seen":[{"kyber_id":23,"signed_id":17,"keys":seen.iter().map(|key|hex(&key.serialize())).collect::<Vec<_>>()}],
  "actual_records_roundtrip":true,"actual_consumed_prekey_stays_absent":true,"actual_kyber_reuse_rejected_after_reload":true,
  "replay_set_mirrors_actual_mark_used_calls_not_private_map_extraction":true})
}
async fn fixture(v:&Value)->Value{
 let seed=v["seed"].as_u64().unwrap();let mut rng=StdRng::seed_from_u64(seed);
 let alice_id=if v["alice_secret"].is_string(){let k=PrivateKey::deserialize(&raw(v,"alice_secret")).unwrap();IdentityKeyPair::new(IdentityKey::new(k.public_key().unwrap()),k)}else if let Some(seed)=v["account_seed"].as_u64(){IdentityKeyPair::generate(&mut StdRng::seed_from_u64(seed))}else{IdentityKeyPair::generate(&mut rng)};let bob_id=if v["bob_secret"].is_string(){let k=PrivateKey::deserialize(&raw(v,"bob_secret")).unwrap();IdentityKeyPair::new(IdentityKey::new(k.public_key().unwrap()),k)}else{IdentityKeyPair::generate(&mut rng)};
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
 let alice_address=ProtocolAddress::new(v["sender_uuid"].as_str().unwrap_or("00112233-4455-6677-8899-aabbccddeeff").into(),1u32.try_into().unwrap());
 let bob_address=ProtocolAddress::new(v["recipient_uuid"].as_str().unwrap_or("ffeeddcc-bbaa-9988-7766-554433221100").into(),1u32.try_into().unwrap());
 if v["send_last_inactive"].as_bool().unwrap_or(false){
  alice_pb.session_management_state=Some(storage::record_structure::SessionManagementState::Tahini(storage::TahiniSessionManagementState{last_act:storage::tahini_session_management_state::LastAct::ReceiveInactive as i32,direction_change_ctr:7}));
 }
 if v["origin_local_new"].as_bool().unwrap_or(false){
  let state=bob_pb.current_session.as_mut().unwrap();state.origin=storage::session_structure::Origin::LocalNew as i32;
  state.pending_pre_key=Some(storage::session_structure::PendingPreKey{pre_key_id:Some(0),signed_pre_key_id:17,base_key:base.public_key.serialize().to_vec(),timestamp:1900000000000});
  state.pending_kyber_pre_key=Some(storage::session_structure::PendingKyberPreKey{pre_key_id:23,ciphertext:vec![31;64]});
 }
 if v["keep_kyber_without_prekey"].as_bool().unwrap_or(false){
  let state=bob_pb.current_session.as_mut().unwrap();state.pending_pre_key=None;
  state.pending_kyber_pre_key=Some(storage::session_structure::PendingKyberPreKey{pre_key_id:23,ciphertext:vec![31;64]});
 }
 if v["origin_without_prekey"].as_bool().unwrap_or(false){bob_pb.current_session.as_mut().unwrap().origin=storage::session_structure::Origin::LocalNew as i32;}
 let mut alice_sessions=InMemSessionStore::new();alice_sessions.store_session(&bob_address,&SessionRecord::deserialize(&alice_pb.encode_to_vec()).unwrap()).await.unwrap();
 let mut bob_sessions=InMemSessionStore::new();bob_sessions.store_session(&alice_address,&SessionRecord::deserialize(&bob_pb.encode_to_vec()).unwrap()).await.unwrap();
 let mut alice_identities=InMemIdentityKeyStore::new(alice_id.clone(),1);let mut bob_identities=InMemIdentityKeyStore::new(bob_id.clone(),2);
 let plaintext=raw(v,"plaintext");assert_eq!(plaintext.len(),80);
 let mut rows=vec![];
 let steps=v["steps"].as_u64().unwrap_or(4);assert!((1..=16).contains(&steps));
 for step in 0..steps{
 let plaintext=if let Some(values)=v["plaintexts"].as_array(){assert_eq!(values.len(),steps as usize);raw(&json!({"plain":values[step as usize]}),"plain")}else{plaintext.clone()};assert_eq!(plaintext.len(),80);
 let before_record=bob_sessions.load_session(&alice_address).await.unwrap().unwrap();let before_pb=record(&before_record);let old=before_pb.current_session.as_ref().unwrap();
 let old_sender=sender(old);let old_receivers=receivers(old);let old_pq=receiving_pq(old);
 let current_alice=alice_sessions.load_session(&bob_address).await.unwrap().unwrap();let alice_pb=record(&current_alice);
 let sender_chain_before=alice_pb.current_session.as_ref().unwrap().sender_chain.as_ref().unwrap().chain_key.as_ref().unwrap().key.clone();
 let pqr_probe=spqr::send(&alice_pb.current_session.as_ref().unwrap().pq_ratchet_state,&mut rng.clone()).unwrap();
 let message=message_encrypt(&plaintext,&bob_address,&alice_address,&mut alice_sessions,&mut alice_identities,std::time::SystemTime::UNIX_EPOCH+std::time::Duration::from_secs(1900000000),&mut rng).await.unwrap();
 assert_eq!(message.message_type(),CiphertextMessageType::Whisper);let wire=if let Some(wires)=v["wires"].as_array(){assert_eq!(wires.len(),steps as usize);raw(&json!({"wire":wires[step as usize]}),"wire")}else{message.serialize().to_vec()};let message=SignalMessage::try_from(wire.as_slice()).unwrap();assert_eq!(message.counter(),step as u32);
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
 if step==0{assert_eq!(post.sender_chain.as_ref().unwrap().sender_ratchet_key_private,fresh.private_key.serialize());}else{assert_eq!(sender(old),sender(post));}
 let computed=if step==0{[fresh.private_key.serialize().to_vec(),fresh.public_key.serialize()[1..].to_vec(),receiving.to_vec(),sending.to_vec()].concat()}else{vec![0;128]};
 let encoded_wire=[vec![255],(wire.len()as u16).to_be_bytes().to_vec(),wire.to_vec(),vec![0;256-wire.len()]].concat();
 let input=[old_sender,old_receivers,old_pq,alice_id.public_key().serialize()[1..].to_vec(),bob_id.public_key().serialize()[1..].to_vec(),computed,encoded_wire].concat();
 let expected=[vec![255],sender(post),receivers(post),receiving_pq(post),vec![0,80],plaintext.clone()].concat();
 let updated=session_projection::apply_result(&before_pb,&expected).unwrap();
 let mut rejected=expected.clone();rejected[0]=0;
 assert_eq!(session_projection::apply_result(&before_pb,&rejected).unwrap(),before_pb);
 rejected[0]=1;assert!(session_projection::apply_result(&before_pb,&rejected).is_err());
 assert!(session_projection::apply_receive(&before_pb,&expected[1..525]).is_err());
 let mut retained=before_pb.clone();retained.previous_sessions.push(before_pb.current_session.as_ref().unwrap().encode_to_vec());
 assert_eq!(session_projection::apply_result(&retained,&expected).unwrap().previous_sessions,retained.previous_sessions);
 let unrelated=before_pb.encode_to_vec();let mut conversations=std::collections::BTreeMap::from([(0,before_pb.clone()),(1,before_pb.clone())]);
 conversations.insert(0,updated.clone());assert_eq!(conversations[&1].encode_to_vec(),unrelated);
 assert_eq!(updated,after,"canonical full-record update mismatch");
 let reloaded=SessionRecord::deserialize(&updated.encode_to_vec()).unwrap();
 assert_eq!(reloaded.serialize().unwrap(),SessionRecord::deserialize(&after.encode_to_vec()).unwrap().serialize().unwrap());
 let restored=record(&reloaded);let restored=restored.current_session.as_ref().unwrap();
 assert_eq!([sender(restored),receivers(restored),receiving_pq(restored)].concat(),expected[1..526]);
 let sent_record=alice_sessions.load_session(&bob_address).await.unwrap().unwrap();let sent_pb=record(&sent_record);let sent=sent_pb.current_session.as_ref().unwrap();
 let sent_selected=[sender(sent),receivers(sent),receiving_pq(sent)].concat();
 let sent_pq=pqr::PqRatchetState::decode(sent.pq_ratchet_state.as_slice()).unwrap();let sent_chain=sent_pq.chain.as_ref().unwrap().links[0].send.as_ref().unwrap();
 let sent_prefix=[vec![255],sent.sender_chain.as_ref().unwrap().chain_key.as_ref().unwrap().key.clone(),sent.sender_chain.as_ref().unwrap().chain_key.as_ref().unwrap().index.to_be_bytes().to_vec(),sent_chain.next.clone(),sent_chain.ctr.to_be_bytes().to_vec(),vec![0;8]].concat();
 assert_eq!(session_send_projection::apply(&alice_pb,&sent_prefix).unwrap(),sent_pb,"canonical sender mismatch");
 let reloaded=SessionRecord::deserialize(&sent_pb.encode_to_vec()).unwrap();assert_eq!(record(&reloaded),sent_pb);
 rows.push(json!({"peer_identity":hex(&[bob_id.private_key().serialize().to_vec(),bob_id.public_key().serialize().to_vec()].concat()),"account_identity":hex(&[alice_id.private_key().serialize().to_vec(),alice_id.public_key().serialize().to_vec()].concat()),"sender_selected_before":hex(&[sender(alice_pb.current_session.as_ref().unwrap()),receivers(alice_pb.current_session.as_ref().unwrap()),receiving_pq(alice_pb.current_session.as_ref().unwrap())].concat()),"sender_record_before":hex(&alice_pb.encode_to_vec()),"sender_result":hex(&sent_prefix),"sender_record_after":hex(&sent_pb.encode_to_vec()),"sender_selected_after":hex(&sent_selected),"record_before":hex(&before_pb.encode_to_vec()),"record_after":hex(&after.encode_to_vec()),"canonical_record_projection_reload":true,"unrelated_record_retained":true,"rejected_result_preserved_record":true,"counter":step,"root_private_preserved":step>0,"input":hex(&input),"expected":hex(&expected),"wire_bytes":wire.len(),"sender_chain_before":hex(&sender_chain_before),"actual_pq_key":hex(&pqr_probe.key.unwrap()),"actual_PQXDH_initialization":true,"selected_PQR_phase_override":true,"actual_new_DH_message_decrypt":true,"tampered_MAC_preserved_actual_store":true}));
 let after_bytes=bob_sessions.load_session(&alice_address).await.unwrap().unwrap().serialize().unwrap();
 assert!(message_decrypt_signal(&message,&alice_address,&bob_address,&mut bob_sessions,&mut bob_identities,&mut receive_rng).await.is_err());
 assert_eq!(bob_sessions.load_session(&alice_address).await.unwrap().unwrap().serialize().unwrap(),after_bytes);
 }
 json!({"rows":rows,"global_stores":global_stores(&alice_id,bob_id.identity_key(),&bob_address,seed,&v["extra_trusted_peers"]).await,"actual_replay_and_MAC_failures_preserved_store":true})
}
fn main(){let rt=tokio::runtime::Builder::new_current_thread().build().unwrap();for line in io::stdin().lock().lines(){let v:Value=serde_json::from_str(&line.unwrap()).unwrap();println!("{}",if v["mode"]=="identity"{identity_fixture(&v)}else{rt.block_on(fixture(&v))});}}

// Same actual SS certificate/key-generation APIs, with explicit NEW sender UUID.
fn identity_fixture(v:&Value)->Value{
 let seed=v["seed"].as_u64().unwrap();let mut rng=StdRng::seed_from_u64(seed);
 let root=KeyPair::generate(&mut rng);let signer=KeyPair::generate(&mut rng);let sender=IdentityKeyPair::generate(&mut rng);let recipient=IdentityKeyPair::generate(&mut rng);
 let uuid=v["sender_uuid"].as_str().unwrap();let server=ServerCertificate::new(1,signer.public_key,&root.private_key,&mut rng).unwrap();
 let cert=SenderCertificate::new(uuid.into(),None,*sender.public_key(),1u32.try_into().unwrap(),Timestamp::from_epoch_millis(2000000000000),server,&signer.private_key,&mut rng).unwrap();
 assert!(cert.validate(&root.public_key,Timestamp::from_epoch_millis(1900000000000)).unwrap());
 json!({"sender_uuid":uuid,"sender_secret":hex(&sender.private_key().serialize()),"sender_identity65":hex(&[sender.private_key().serialize().to_vec(),sender.public_key().serialize().to_vec()].concat()),"recipient_secret":hex(&recipient.private_key().serialize()),"recipient_identity65":hex(&[recipient.private_key().serialize().to_vec(),recipient.public_key().serialize().to_vec()].concat()),"root_public":hex(&root.public_key.serialize()),"certificate":hex(cert.serialized().unwrap()),"certificate_validated":true})
}
