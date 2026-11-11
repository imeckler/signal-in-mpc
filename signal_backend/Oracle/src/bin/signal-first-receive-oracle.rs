//! Test oracle for the RECEIVE path of a new contact's first message.
//! A real libsignal v0.106.1 SENDER (Alice) establishes a session from the
//! test recipient's prekey bundle and produces sealed-sender v1 envelopes
//! carrying PreKeySignalMessages. The recipient's private keys are fixture
//! values printed for the test (never production keys). The same process then
//! judges a reply produced from the recipient's computed session state, and
//! runs an unmodified libsignal recipient on the first envelope for comparison.
//! Nothing here contacts a network service.
use std::io::{self,BufRead};
use libsignal_protocol::*;
use rand::{SeedableRng,rngs::StdRng};
use serde_json::{Value,json};
use prost::Message;
#[allow(dead_code)]mod storage {include!(concat!(env!("OUT_DIR"),"/signal.proto.storage.rs"));}
#[derive(Clone,PartialEq,Message)]
struct CertificateBody {
 #[prost(string,optional,tag="1")]e164:Option<String>,
 #[prost(uint32,optional,tag="2")]device:Option<u32>,
 #[prost(fixed64,optional,tag="3")]expires:Option<u64>,
 #[prost(bytes="vec",optional,tag="4")]identity_key:Option<Vec<u8>>,
 #[prost(bytes="vec",optional,tag="5")]signer_certificate:Option<Vec<u8>>,
 #[prost(bytes="vec",optional,tag="7")]uuid_bytes:Option<Vec<u8>>,
 #[prost(uint32,optional,tag="8")]signer_id:Option<u32>,
}
#[derive(Clone,PartialEq,Message)]
struct Signed {
 #[prost(bytes="vec",optional,tag="1")]certificate:Option<Vec<u8>>,
 #[prost(bytes="vec",optional,tag="2")]signature:Option<Vec<u8>>,
}
fn hex(x:&[u8])->String{x.iter().map(|b|format!("{b:02x}")).collect()}
fn raw(v:&Value,k:&str)->Vec<u8>{let s=v[k].as_str().unwrap();assert_eq!(s.len()%2,0);(0..s.len()).step_by(2).map(|i|u8::from_str_radix(&s[i..i+2],16).unwrap()).collect()}
const ALICE:&str="a2000000-0000-4000-8000-000000000001";
const BOB:&str="b2000000-0000-4000-8000-000000000002";
const TEST_SERVER_ID:u32=0x7357C357;
struct Peer{
 alice_address:ProtocolAddress,bob_address:ProtocolAddress,
 sessions:InMemSessionStore,identities:InMemIdentityKeyStore,kem:kem::KeyPair,rng:StdRng,
}
impl Peer{
 async fn new(v:&Value)->(Self,Value){
  let seed=v["seed"].as_u64().unwrap();let mut rng=StdRng::seed_from_u64(seed);
  let one_time=v["one_time"].as_bool().unwrap();let style=v["style"].as_str().unwrap();let with_e164=v["e164"].as_bool().unwrap();
  let count=v["count"].as_u64().unwrap();let hint=v["hint"].as_bool().unwrap();let plaintext=raw(v,"plaintext");
  let alice=IdentityKeyPair::generate(&mut rng);let bob=IdentityKeyPair::generate(&mut rng);
  let one=KeyPair::generate(&mut rng);let signed_pair=KeyPair::generate(&mut rng);let kem_pair=kem::KeyPair::generate(kem::KeyType::Kyber1024,&mut rng);
  let signed_sig=bob.private_key().calculate_signature(&signed_pair.public_key.serialize(),&mut rng).unwrap();
  let kem_sig=bob.private_key().calculate_signature(&kem_pair.public_key.serialize(),&mut rng).unwrap();
  let ids=(v["one_time_id"].as_u64().unwrap() as u32,v["signed_id"].as_u64().unwrap() as u32,v["kyber_id"].as_u64().unwrap() as u32);
  let alice_registration=v["alice_registration"].as_u64().unwrap() as u32;let bob_registration=2u32;
  let bundle:PreKeyBundle=PreKeyBundleContent{registration_id:Some(bob_registration),device_id:Some(1u32.try_into().unwrap()),
   pre_key_id:if one_time{Some(ids.0.into())}else{None},pre_key_public:if one_time{Some(one.public_key)}else{None},
   signed_pre_key_id:Some(ids.1.into()),signed_pre_key_public:Some(signed_pair.public_key),signed_pre_key_signature:Some(signed_sig.to_vec()),
   identity_key:Some(*bob.identity_key()),kyber_pre_key_id:Some(ids.2.into()),kyber_pre_key_public:Some(kem_pair.public_key.clone()),kyber_pre_key_signature:Some(kem_sig.to_vec())}.try_into().unwrap();
  let alice_device=v["alice_device"].as_u64().unwrap() as u32;
  let alice_address=ProtocolAddress::new(ALICE.into(),alice_device.try_into().unwrap());let bob_address=ProtocolAddress::new(BOB.into(),1u32.try_into().unwrap());
  // Certificates. The reference style uses libsignal's built-in test server certificate.
  let expires=v["expires"].as_u64().unwrap();
  let (root_public,server_private,server_public,server_certificate)=if style=="reference"{
   let root=PrivateKey::deserialize(&[0u8;32]).unwrap();let server=PrivateKey::deserialize(&[0xFFu8;32]).unwrap();
   (root.public_key().unwrap(),server,server.public_key().unwrap(),vec![])
  }else{
   let root=KeyPair::generate(&mut rng);let signer=KeyPair::generate(&mut rng);
   let server=ServerCertificate::new(v["server_id"].as_u64().unwrap() as u32,signer.public_key,&root.private_key,&mut rng).unwrap();
   (root.public_key,signer.private_key,signer.public_key,server.serialized().unwrap().to_vec())
  };
  let e164=if with_e164{Some("+14155550123".to_string())}else{None};
  let certificate=if style=="libsignal"{
   SenderCertificate::new(ALICE.into(),e164,*alice.public_key(),alice_device.try_into().unwrap(),Timestamp::from_epoch_millis(expires),
    ServerCertificate::deserialize(&server_certificate).unwrap(),&server_private,&mut rng).unwrap()
  }else{
   let uuid=libsignal_core::ServiceId::parse_from_service_id_string(ALICE).unwrap().service_id_fixed_width_binary()[1..].to_vec();
   let body=CertificateBody{e164,device:Some(alice_device),expires:Some(expires),identity_key:Some(alice.public_key().serialize().to_vec()),
    signer_certificate:if style=="server"{Some(server_certificate.clone())}else{None},uuid_bytes:Some(uuid),
    signer_id:if style=="reference"{Some(TEST_SERVER_ID)}else{None}}.encode_to_vec();
   let signature=server_private.calculate_signature(&body,&mut rng).unwrap().to_vec();
   SenderCertificate::deserialize(&Signed{certificate:Some(body),signature:Some(signature)}.encode_to_vec()).unwrap()
  };
  let now=Timestamp::from_epoch_millis(v["now"].as_u64().unwrap());
  assert!(certificate.validate(&root_public,now).unwrap());
  // Alice: session from the bundle, then `count` messages, each sealed.
  let mut sessions=InMemSessionStore::new();let mut identities=InMemIdentityKeyStore::new(alice.clone(),alice_registration);
  let time=std::time::SystemTime::UNIX_EPOCH+std::time::Duration::from_millis(v["now"].as_u64().unwrap());
  process_prekey_bundle(&bob_address,&alice_address,&mut sessions,&mut identities,&bundle,time,&mut rng).await.unwrap();
  let mut envelopes=vec![];let mut wires=vec![];
  for _ in 0..count{
   let message=message_encrypt(&plaintext,&bob_address,&alice_address,&mut sessions,&mut identities,time,&mut rng).await.unwrap();
   assert_eq!(message.message_type(),CiphertextMessageType::PreKey);
   let usmc=UnidentifiedSenderMessageContent::new(CiphertextMessageType::PreKey,certificate.clone(),message.serialize().to_vec(),
    if hint{ContentHint::Resendable}else{ContentHint::Default},None).unwrap();
   envelopes.push(hex(&sealed_sender_encrypt_from_usmc(&bob_address,&usmc,&identities,&mut rng).await.unwrap()));
   wires.push(hex(message.serialize()));
  }
  // An unmodified libsignal recipient on the first envelope.
  let mut bob_sessions=InMemSessionStore::new();let mut bob_identities=InMemIdentityKeyStore::new(bob.clone(),bob_registration);
  let mut prekeys=InMemPreKeyStore::new();if one_time{prekeys.save_pre_key(ids.0.into(),&PreKeyRecord::new(ids.0.into(),&one)).await.unwrap();}
  let mut signed=InMemSignedPreKeyStore::new();signed.save_signed_pre_key(ids.1.into(),&SignedPreKeyRecord::new(ids.1.into(),now,&signed_pair,&signed_sig)).await.unwrap();
  let mut kyber=InMemKyberPreKeyStore::new();kyber.save_kyber_pre_key(ids.2.into(),&KyberPreKeyRecord::new(ids.2.into(),now,&kem_pair,&kem_sig)).await.unwrap();
  let first=raw(&json!({"w":envelopes[0]}),"w");
  let decrypted=sealed_sender_decrypt(&first,&root_public,now,None,BOB.into(),1u32.try_into().unwrap(),&mut bob_identities,&mut bob_sessions,&mut prekeys,&signed,&mut kyber).await.unwrap();
  let record=bob_sessions.load_session(&alice_address).await.unwrap().unwrap().serialize().unwrap();
  let state=storage::RecordStructure::decode(record.as_slice()).unwrap().current_session.unwrap();
  let chain=&state.receiver_chains[0];let chain_key=chain.chain_key.as_ref().unwrap();
  let out=json!({
   "bob_identity_private":hex(&bob.private_key().serialize()),"bob_identity":hex(&bob.public_key().serialize()),
   "signed_prekey_private":hex(&signed_pair.private_key.serialize()),"one_time_prekey_private":hex(&one.private_key.serialize()),
   "alice_identity":hex(&alice.public_key().serialize()),"alice_uuid":ALICE,"bob_uuid":BOB,"alice_device":alice_device,
   "alice_registration":alice_registration,"certificate":hex(certificate.serialized().unwrap()),
   "server_certificate":hex(&server_certificate),"server_public":hex(&server_public.serialize()),"server_id":if style=="reference"{TEST_SERVER_ID}else{v["server_id"].as_u64().unwrap() as u32},
   "trust_root":hex(&root_public.serialize()),"envelopes":envelopes,"prekey_messages":wires,
   "libsignal_recipient":{"plaintext":hex(&decrypted.message),"sender_uuid":decrypted.sender_uuid,"device":u32::from(decrypted.device_id),
    "receiver_ratchet_key":hex(&chain.sender_ratchet_key),"receiver_chain_key":hex(&chain_key.key),"receiver_chain_index":chain_key.index,
    "remote_registration":state.remote_registration_id,"previous_counter":state.previous_counter,"sender_chain_index":state.sender_chain.as_ref().unwrap().chain_key.as_ref().unwrap().index}});
  (Self{alice_address,bob_address,sessions,identities,kem:kem_pair,rng},out)
 }
 fn decapsulate(&self,v:&Value)->Value{
  match self.kem.secret_key.decapsulate(&raw(v,"ciphertext").into_boxed_slice()){Ok(secret)=>json!({"secret":hex(&secret)}),Err(_)=>json!({"error":"decapsulate"})}
 }
 /// Alice receives a SignalMessage produced from the recipient's computed state.
 async fn reply(&mut self,v:&Value)->Value{
  let message=match SignalMessage::try_from(raw(v,"wire").as_slice()){Ok(m)=>m,Err(_)=>return json!({"accepted":false,"error":"decode"})};
  match message_decrypt_signal(&message,&self.bob_address,&self.alice_address,&mut self.sessions,&mut self.identities,&mut self.rng).await{
   Ok(plaintext)=>json!({"accepted":true,"plaintext":hex(&plaintext)}),Err(error)=>json!({"accepted":false,"error":format!("{error}")})}
 }
}
fn main(){let rt=tokio::runtime::Builder::new_current_thread().build().unwrap();let mut peer=None;
 for line in io::stdin().lock().lines(){let v:Value=serde_json::from_str(&line.unwrap()).unwrap();
  let out=match v["mode"].as_str().unwrap(){
   "init"=>{let(p,out)=rt.block_on(Peer::new(&v));peer=Some(p);out},
   "decapsulate"=>peer.as_ref().unwrap().decapsulate(&v),
   "reply"=>rt.block_on(peer.as_mut().unwrap().reply(&v)),
   _=>panic!("unsupported mode")};
  println!("{}",out);}}
