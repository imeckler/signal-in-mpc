// Public fixture generator calling the unchanged pinned full SSv1 API.
use libsignal_protocol::*;
use rand::{SeedableRng,rngs::StdRng};
use serde_json::{Value,json};
use crate::{raw,hex};
pub async fn fixture(v:&Value)->Value{
 let seed=v["seed"].as_u64().unwrap();let mut rng=StdRng::seed_from_u64(seed);
 let root=KeyPair::generate(&mut rng);let signer=KeyPair::generate(&mut rng);
 let sender=IdentityKeyPair::generate(&mut rng);let recipient=IdentityKeyPair::generate(&mut rng);
 let server=ServerCertificate::new(1,signer.public_key,&root.private_key,&mut rng).unwrap();
 let certificate=SenderCertificate::new("00112233-4455-6677-8899-aabbccddeeff".into(),None,
  *sender.public_key(),libsignal_core::DeviceId::new(1).unwrap(),Timestamp::from_epoch_millis(2000000000000),
  server,&signer.private_key,&mut rng).unwrap();
 assert!(certificate.validate(&root.public_key,Timestamp::from_epoch_millis(1900000000000)).unwrap());
 let inner=raw(v,"inner");
 let usmc=UnidentifiedSenderMessageContent::new(CiphertextMessageType::Whisper,certificate.clone(),
  inner.clone(),ContentHint::Default,None).unwrap();
 let address=ProtocolAddress::new("ffeeddcc-bbaa-9988-7766-554433221100".into(),libsignal_core::DeviceId::new(1).unwrap());
 let mut store=InMemIdentityKeyStore::new(sender.clone(),1);
 store.save_identity(&address,recipient.identity_key()).await.unwrap();
 let mut ephemeral_rng=StdRng::seed_from_u64(seed+1000);let mut clone=ephemeral_rng.clone();
 let ephemeral=KeyPair::generate(&mut clone);
 let edh=ephemeral.private_key.calculate_agreement(recipient.public_key()).unwrap();
 let sdh=sender.private_key().calculate_agreement(recipient.public_key()).unwrap();
 let wire=sealed_sender_encrypt_from_usmc(&address,&usmc,&store,&mut ephemeral_rng).await.unwrap();
 let receiver_store=InMemIdentityKeyStore::new(recipient.clone(),2);
 let decoded=sealed_sender_decrypt_to_usmc(&wire,&receiver_store).await.unwrap();
 assert_eq!(decoded.contents().unwrap(),inner);
 assert!(decoded.sender().unwrap().validate(&root.public_key,Timestamp::from_epoch_millis(1900000000000)).unwrap());
 let mut corrupted=wire.clone();let last=corrupted.len()-1;corrupted[last]^=1;
 assert!(sealed_sender_decrypt_to_usmc(&corrupted,&receiver_store).await.is_err());
 let cert=certificate.serialized().unwrap();
 let mut input=vec![];
 input.extend_from_slice(&recipient.public_key().serialize()[1..]);
 input.extend_from_slice(&ephemeral.public_key.serialize()[1..]);
 input.extend_from_slice(&sender.public_key().serialize()[1..]);
 input.extend_from_slice(&edh);input.extend_from_slice(&sdh);input.extend_from_slice(cert);input.extend_from_slice(&inner);
 json!({"input":hex(&input),"wire":hex(&wire),"certificate_size":cert.len(),"inner_size":inner.len(),
 "usmc":hex(usmc.serialized().unwrap()),"sender_secret":hex(&sender.private_key().serialize()),"recipient_secret":hex(&recipient.private_key().serialize()),"root_public":hex(&root.public_key.serialize()),"fixture_certificate_validated":true,"actual_decrypt_to_usmc_roundtrip":true,"actual_tampered_envelope_rejected":true})
}

pub async fn decrypt(v:&Value)->Value{
 let secret=PrivateKey::deserialize(&raw(v,"recipient_secret")).unwrap();
 let identity=IdentityKeyPair::new(IdentityKey::new(secret.public_key().unwrap()),secret);
 let store=InMemIdentityKeyStore::new(identity,2);
 let result=sealed_sender_decrypt_to_usmc(&raw(v,"wire"),&store).await;
 match result{
  Ok(usmc)=>{
   let root=PublicKey::deserialize(&raw(v,"root_public")).unwrap();
   assert!(usmc.sender().unwrap().validate(&root,Timestamp::from_epoch_millis(1900000000000)).unwrap());
   json!({"inner":hex(usmc.contents().unwrap()),"certificate_valid":true})
  },
  Err(error)=>json!({"error":format!("{error:?}")})
 }
}
