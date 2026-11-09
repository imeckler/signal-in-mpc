// PUBLIC disposable peer smoke only. Unchanged pinned SSv1 APIs; no MPC input.
use std::io::{self,BufRead};
use libsignal_protocol::*;
use rand::{SeedableRng,rngs::StdRng};
use serde_json::{Value,json};
fn raw(v:&Value,k:&str)->Vec<u8>{let s=v[k].as_str().unwrap();(0..s.len()).step_by(2).map(|i|u8::from_str_radix(&s[i..i+2],16).unwrap()).collect()}
fn hex(v:&[u8])->String{v.iter().map(|b|format!("{b:02x}")).collect()}
async fn run(v:Value)->Value{
 if v["mode"]=="decrypt"{
  let private=PrivateKey::deserialize(&raw(&v,"recipient_secret")).unwrap();let pair=IdentityKeyPair::new(IdentityKey::new(private.public_key().unwrap()),private);let store=InMemIdentityKeyStore::new(pair,2);
  let content=sealed_sender_decrypt_to_usmc(&raw(&v,"wire"),&store).await.unwrap();let cert=content.sender().unwrap();let root=PublicKey::deserialize(&raw(&v,"root_public")).unwrap();assert!(cert.validate(&root,Timestamp::from_epoch_millis(1900000000000)).unwrap());
  return json!({"inner":hex(content.contents().unwrap()),"sender_uuid":cert.sender_uuid().unwrap(),"sender_key":hex(&cert.key().unwrap().serialize()),"certificate_valid":true});
 }
 let identity=raw(&v,"sender_identity65");assert!(identity.len()==65);let private=PrivateKey::deserialize(&identity[..32]).unwrap();let pair=IdentityKeyPair::new(IdentityKey::new(private.public_key().unwrap()),private);assert!(pair.public_key().serialize().as_ref()==&identity[32..]);
 let cert=SenderCertificate::deserialize(&raw(&v,"certificate")).unwrap();assert!(cert.key().unwrap()==*pair.public_key());assert!(cert.sender_uuid().unwrap()==v["sender_uuid"].as_str().unwrap());
 let content=UnidentifiedSenderMessageContent::new(CiphertextMessageType::Whisper,cert,raw(&v,"inner"),ContentHint::Default,None).unwrap();let address=ProtocolAddress::new(v["recipient_uuid"].as_str().unwrap().into(),1u32.try_into().unwrap());let mut store=InMemIdentityKeyStore::new(pair,1);let peer=PublicKey::deserialize(&raw(&v,"recipient_public")).unwrap();store.save_identity(&address,&IdentityKey::new(peer)).await.unwrap();let mut rng=StdRng::seed_from_u64(v["seed"].as_u64().unwrap());
 let wire=sealed_sender_encrypt_from_usmc(&address,&content,&store,&mut rng).await.unwrap();json!({"wire":hex(&wire)})
}
fn main(){let rt=tokio::runtime::Builder::new_current_thread().build().unwrap();for line in io::stdin().lock().lines(){let value:Value=serde_json::from_str(&line.unwrap()).unwrap();println!("{}",rt.block_on(run(value)));}}
