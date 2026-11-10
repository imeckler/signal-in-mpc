// Calls unchanged actual libsignal constructors, key APIs and validation prefix.
use std::{io::{self,BufRead},cell::RefCell,rc::Rc,sync::Arc,task::{Context,Poll,Wake,Waker},future::Future};
use libsignal_protocol::*;
use rand::{RngCore,SeedableRng};
use serde_json::{Value,json};
type R<T> = Result<T,SignalProtocolError>;
fn bytes(s:&str)->Vec<u8>{assert_eq!(s.len()%2,0);(0..s.len()).step_by(2).map(|i|u8::from_str_radix(&s[i..i+2],16).unwrap()).collect()}
fn hex(x:&[u8])->String{x.iter().map(|b|format!("{b:02x}")).collect()}
fn raw(v:&Value,k:&str)->Vec<u8>{bytes(v[k].as_str().unwrap())}
fn meta(v:&Value,k:&str,default:u32)->u32{v[k].as_u64().map(|x|u32::try_from(x).unwrap()).unwrap_or(default)}
fn key_error(e:&str)->u8{if e.contains("no key type") {1} else if e.contains("bad key type")||e.contains("bad KEM key type"){2}else{3}}
fn construct(v:&Value)->R<PreKeyBundle>{
 let flags:Vec<u8>=v["flags"].as_array().unwrap().iter().map(|x|x.as_u64().unwrap() as u8).collect();let has=|i:usize|flags[i]==1;
 let ec=has(5).then(||PublicKey::deserialize(&raw(v,"ec")).unwrap());
 let optional=has(3).then(||PublicKey::deserialize(&raw(v,if v["optional_key"].is_string(){"optional_key"}else{"ec"})).unwrap());
 let identity=has(7).then(||IdentityKey::decode(&raw(v,"identity")).unwrap());let pq=has(9).then(||kem::PublicKey::deserialize(&raw(v,"pq")).unwrap());
 PreKeyBundleContent{
  registration_id:has(0).then(||meta(v,"registration",0xffffffff)),device_id:has(1).then(||DeviceId::new(meta(v,"device",127) as u8).unwrap()),
  pre_key_id:has(2).then(||meta(v,"optional_id",0xffffffff).into()),pre_key_public:optional,
  signed_pre_key_id:has(4).then(||meta(v,"signed_id",0xffffffff).into()),signed_pre_key_public:ec,
  signed_pre_key_signature:has(6).then(||raw(v,"ec_sig")),identity_key:identity,
  kyber_pre_key_id:has(8).then(||meta(v,"pq_id",0xffffffff).into()),kyber_pre_key_public:pq,
  kyber_pre_key_signature:has(10).then(||raw(v,"pq_sig")),
 }.try_into()
}
const MISSING:[&str;9]=["registration_id","device_id","signed_pre_key_id","signed_pre_key_public","signed_pre_key_signature","kyber_pre_key_id","kyber_pre_key_public","kyber_pre_key_signature","identity_key"];
fn missing(e:&SignalProtocolError)->u8{match e{SignalProtocolError::InvalidArgument(s)=>MISSING.iter().position(|k|s==&format!("{k} is required")).unwrap() as u8+1,_=>panic!("unexpected constructor error {e}")}}
fn metadata(b:&PreKeyBundle)->Vec<u8>{
 let mut out=vec![];out.extend_from_slice(&b.registration_id().unwrap().to_be_bytes());out.push(u8::from(b.device_id().unwrap()));
 let id:u32=b.pre_key_id().unwrap().map(Into::into).unwrap_or(0);out.extend_from_slice(&id.to_be_bytes());
 let id:u32=b.signed_pre_key_id().unwrap().into();out.extend_from_slice(&id.to_be_bytes());
 let id:u32=b.kyber_pre_key_id().unwrap().into();out.extend_from_slice(&id.to_be_bytes());out
}
struct IdentityFixture{code:u8,expected:IdentityKey,trace:Rc<RefCell<Vec<String>>>}
#[async_trait::async_trait(?Send)]
impl IdentityKeyStore for IdentityFixture{
 async fn get_identity_key_pair(&self)->R<IdentityKeyPair>{panic!("past validation prefix")}
 async fn get_local_registration_id(&self)->R<u32>{panic!("past validation prefix")}
 async fn save_identity(&mut self,_:&ProtocolAddress,_:&IdentityKey)->R<IdentityChange>{panic!("unexpected identity write")}
 async fn get_identity(&self,_:&ProtocolAddress)->R<Option<IdentityKey>>{panic!("unexpected lookup")}
 async fn is_trusted_identity(&self,_:&ProtocolAddress,key:&IdentityKey,direction:Direction)->R<bool>{
  assert_eq!(*key,self.expected);assert_eq!(direction,Direction::Sending);self.trace.borrow_mut().push("trust_sending".into());
  match self.code{0=>Ok(true),1=>Ok(false),2=>Err(SignalProtocolError::InvalidState("trust_fixture","external trust callback failed".into())),_=>panic!("trust code")}
 }
}
struct SessionFixture{trace:Rc<RefCell<Vec<String>>>}
#[async_trait::async_trait(?Send)]
impl SessionStore for SessionFixture{
 async fn load_session(&self,_:&ProtocolAddress)->R<Option<SessionRecord>>{
  self.trace.borrow_mut().push("load_session_boundary".into());Err(SignalProtocolError::InvalidState("after_validation","sentinel".into()))
 }
 async fn store_session(&mut self,_:&ProtocolAddress,_:&SessionRecord)->R<()>{panic!("unexpected session write")}
}
struct Noop;impl Wake for Noop{fn wake(self:Arc<Self>){}}
fn ready<F:Future>(f:F)->F::Output{let w=Waker::from(Arc::new(Noop));let mut c=Context::from_waker(&w);match Box::pin(f).as_mut().poll(&mut c){Poll::Ready(v)=>v,Poll::Pending=>panic!("fixture unexpectedly pending")}}
fn run(v:Value)->Value{
 match v["mode"].as_str().unwrap(){
  "ec"=>{let r=raw(&v,"raw");match PublicKey::deserialize(&r){Ok(k)=>json!({"code":0,"wire":hex(&k.serialize())}),Err(e)=>json!({"code":key_error(&e.to_string()),"error":e.to_string()})}},
  "kem"=>{let r=raw(&v,"raw");match kem::PublicKey::deserialize(&r){Ok(k)=>json!({"code":0,"wire":hex(&k.serialize())}),Err(e)=>json!({"code":key_error(&e.to_string()),"error":e.to_string()})}},
  "device"=>{let n=v["value"].as_u64().unwrap() as u32;match DeviceId::try_from(n){Ok(d)=>json!({"valid":true,"value":u8::from(d)}),Err(_)=>json!({"valid":false})}},
  "construct"=>{match construct(&v){Ok(b)=>json!({"code":0,"optional":b.pre_key_id().unwrap().is_some(),"metadata":metadata(&b)}),Err(e)=>json!({"code":missing(&e),"error":e.to_string()})}},
  "validate"=>{
   let b=match construct(&v){Ok(b)=>b,Err(e)=>return json!({"code":missing(&e),"trace":[],"error":e.to_string()})};
   let trace=Rc::new(RefCell::new(vec![]));let mut store=SessionFixture{trace:trace.clone()};
   let mut ids=IdentityFixture{code:v["trust"].as_u64().unwrap() as u8,expected:*b.identity_key().unwrap(),trace:trace.clone()};
   let remote=ProtocolAddress::new("public fixture remote".into(),DeviceId::new(1).unwrap());let local=ProtocolAddress::new("public fixture local".into(),DeviceId::new(2).unwrap());
   let mut rng=rand::rngs::StdRng::seed_from_u64(71);
   let e=ready(process_prekey_bundle(&remote,&local,&mut store,&mut ids,&b,std::time::UNIX_EPOCH,&mut rng)).unwrap_err();
   let code=match &e{SignalProtocolError::InvalidState("after_validation",_)=>0,SignalProtocolError::InvalidState("trust_fixture",_)=>17,SignalProtocolError::UntrustedIdentity(_)=>16,SignalProtocolError::SignatureValidationFailed=>18,_=>panic!("unexpected prefix outcome {e}")};
   let t=trace.borrow().clone();json!({"code":code,"trace":t,"error":e.to_string(),"metadata":metadata(&b),"optional":b.pre_key_id().unwrap().is_some()})
  },
  "generate"=>{
   let mut rng=rand::rngs::StdRng::seed_from_u64(v["seed"].as_u64().unwrap());let mut b=[0u8;32];rng.fill_bytes(&mut b);
   let id=PrivateKey::deserialize(&b).unwrap();rng.fill_bytes(&mut b);let ec=PrivateKey::deserialize(&b).unwrap().public_key().unwrap().serialize();
   let tag=v["tag"].as_u64().unwrap() as u8;let mut pq=vec![0u8;if tag==7{1185}else{1569}];rng.fill_bytes(&mut pq);pq[0]=tag;let pq=kem::PublicKey::deserialize(&pq).unwrap().serialize();
   json!({"identity":hex(&id.public_key().unwrap().serialize()),"ec":hex(&ec),"pq":hex(&pq),"ec_sig":hex(&id.calculate_signature(&ec,&mut rng).unwrap()),"pq_sig":hex(&id.calculate_signature(&pq,&mut rng).unwrap()),"untagged_ec_sig":hex(&id.calculate_signature(&ec[1..],&mut rng).unwrap()),"untagged_pq_sig":hex(&id.calculate_signature(&pq[1..],&mut rng).unwrap()),"flags":[1,1,1,1,1,1,1,1,1,1,1],"trust":0})
  },
  _=>panic!("mode")
 }
}
fn main(){for line in io::stdin().lock().lines(){let v:Value=serde_json::from_str(&line.unwrap()).unwrap();println!("{}",run(v));}}
