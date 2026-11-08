mod sealed;
mod relay;
// Differential harness only: unchanged pinned libsignal APIs, public fixtures.
use std::io::{self,BufRead};
use libsignal_protocol::{SignalMessage,PublicKey,IdentityKey};
use libsignal_core::{ServiceId,DeviceId};
use serde_json::{Value,json};
fn raw(v:&Value,k:&str)->Vec<u8>{
 let s=v[k].as_str().unwrap();assert_eq!(s.len()%2,0);
 (0..s.len()).step_by(2).map(|i|u8::from_str_radix(&s[i..i+2],16).unwrap()).collect()
}
fn hex(x:&[u8])->String{x.iter().map(|b|format!("{b:02x}")).collect()}
fn key(v:&Value,k:&str)->PublicKey{let mut b=vec![5];b.extend(raw(v,k));PublicKey::deserialize(&b).unwrap()}
async fn decode_h2(wire:Vec<u8>)->Value{
 use tokio::io::AsyncWriteExt;
 let (mut peer,transport)=tokio::io::duplex(65536);
 peer.write_all(b"PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n").await.unwrap();
 peer.write_all(&[0,0,0,4,0,0,0,0,0]).await.unwrap(); // SETTINGS
 peer.write_all(&wire).await.unwrap();
 let mut connection=h2::server::handshake(transport).await.unwrap();
 let (request,_respond)=connection.accept().await.unwrap().unwrap();
 let mut metadata=json!({"method":request.method().as_str(),"path":request.uri().path(),
  "authority":request.uri().authority().unwrap().as_str(),
  "authorization":request.headers()["authorization"].to_str().unwrap(),
  "content_type":request.headers()["content-type"].to_str().unwrap(),
  "te":request.headers()["te"].to_str().unwrap()});
 let driver=tokio::spawn(async move{while connection.accept().await.is_some(){}});
 let mut body=request.into_body();let mut content=vec![];
 while let Some(chunk)=body.data().await{content.extend(chunk.unwrap());}
 metadata["body"]=Value::String(hex(&content));driver.abort();metadata
}
fn main(){for line in io::stdin().lock().lines(){
 let v:Value=serde_json::from_str(&line.unwrap()).unwrap();
 if v["mode"]=="varint"{let mut b=vec![];prost::encoding::encode_varint(v["value"].as_u64().unwrap(),&mut b);println!("{}",json!({"wire":hex(&b)}));continue;}
 if v["mode"]=="check101"{println!("{}",relay::check101(&v));continue;}
 if v["mode"]=="upgrade"{println!("{}",relay::upgrade(&v));continue;}
 if v["mode"]=="sealed_decrypt"{
 let rt=tokio::runtime::Builder::new_current_thread().build().unwrap();
 println!("{}",rt.block_on(sealed::decrypt(&v)));continue;}
 if v["mode"]=="relay"{println!("{}",relay::decode(&v));continue;}
 if v["mode"]=="sealed"{
  let rt=tokio::runtime::Builder::new_current_thread().build().unwrap();
  println!("{}",rt.block_on(sealed::fixture(&v)));continue;
 }
 if v["mode"]=="h2"{
  let rt=tokio::runtime::Builder::new_current_thread().build().unwrap();
  println!("{}",rt.block_on(decode_h2(raw(&v,"wire"))));continue;
 }
 let plain=raw(&v,"plain");let cipher=raw(&v,"cipher_key");let iv=raw(&v,"iv");let mac=raw(&v,"mac_key");
 let ciphertext=signal_crypto::aes_256_cbc_encrypt(&plain,&cipher,&iv).unwrap();
 let sender=IdentityKey::new(key(&v,"sender"));let receiver=IdentityKey::new(key(&v,"receiver"));
 let addr=raw(&v,"addresses");
 let addresses=if addr.is_empty(){None}else{
  let sender=ServiceId::parse_from_service_id_fixed_width_binary(addr[..17].try_into().unwrap()).unwrap();
  let recipient=ServiceId::parse_from_service_id_fixed_width_binary(addr[18..35].try_into().unwrap()).unwrap();
  Some((sender.to_protocol_address(DeviceId::new(addr[17]).unwrap()),recipient.to_protocol_address(DeviceId::new(addr[35]).unwrap())))
 };
 let msg=SignalMessage::new(v["version"].as_u64().unwrap() as u8,&mac,addresses.as_ref().map(|(a,b)|(a,b)),key(&v,"ratchet"),
  v["counter"].as_u64().unwrap() as u32,v["previous"].as_u64().unwrap() as u32,
  &ciphertext,&sender,&receiver,&raw(&v,"pq")).unwrap();
 let parsed=SignalMessage::try_from(msg.serialized());
 if let Ok(ref parsed)=parsed{assert_eq!(signal_crypto::aes_256_cbc_decrypt(parsed.body(),&cipher,&iv).unwrap(),plain);}
 println!("{}",json!({"wire":hex(msg.serialized()),"parse":parsed.map(|_|"ok".to_string()).unwrap_or_else(|e|format!("{e:?}"))}));
}}
