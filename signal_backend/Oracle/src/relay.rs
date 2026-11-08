use prost::Message;
use serde_json::{Value,json};
use base64::{Engine,engine::general_purpose::STANDARD};
use crate::{raw,hex};
mod proto{include!(concat!(env!("OUT_DIR"),"/signal.proto.chat_websocket.rs"));}
pub fn decode(v:&Value)->Value{
 let wire=raw(v,"wire");assert_eq!(wire[0],0x82);assert_ne!(wire[1]&128,0);
 let (length,offset)=if wire[1]&127==126{(u16::from_be_bytes([wire[2],wire[3]]) as usize,4)}else{((wire[1]&127)as usize,2)};
 assert_eq!(wire.len(),offset+4+length);
 let mask=&wire[offset..offset+4];let payload:Vec<u8>=wire[offset+4..].iter().enumerate().map(|(i,b)|b^mask[i%4]).collect();
 let message=proto::WebSocketMessage::decode(payload.as_slice()).unwrap();assert_eq!(message.r#type,Some(1));
 assert!(message.response.is_none());let request=message.request.unwrap();assert_eq!(request.verb.as_deref(),Some("PUT"));
 let body:Value=serde_json::from_slice(request.body.as_deref().unwrap()).unwrap();
 let ciphertext=STANDARD.decode(body["messages"][0]["content"].as_str().unwrap()).unwrap();
 let access=request.headers.iter().find_map(|s|s.strip_prefix("unidentified-access-key: ")).unwrap();
 let key=STANDARD.decode(access).unwrap();
 json!({"path":request.path,"id":request.id,"body":body,"ciphertext":hex(&ciphertext),"access_key":hex(&key),"headers":request.headers})
}

pub fn upgrade(v:&Value)->Value{
 let wire=raw(v,"wire");let mut headers=[httparse::EMPTY_HEADER;32];
 let mut request=httparse::Request::new(&mut headers);assert!(request.parse(&wire).unwrap().is_complete());
 assert_eq!(request.method,Some("GET"));assert_eq!(request.path,Some("/v1/websocket/"));
 let mut builder=tungstenite::http::Request::builder().method("GET").uri("/v1/websocket/");
 for h in request.headers.iter(){builder=builder.header(h.name,h.value);}
 let request=builder.body(()).unwrap();
 let response=tungstenite::handshake::server::create_response(&request).unwrap();
 let basic=request.headers()["authorization"].to_str().unwrap().strip_prefix("Basic ").unwrap();
 json!({"status":response.status().as_u16(),"credentials":hex(&STANDARD.decode(basic).unwrap()),
 "key":request.headers()["sec-websocket-key"].to_str().unwrap(),
 "accept":response.headers()["sec-websocket-accept"].to_str().unwrap()})
}

// Public-fixture-only client handshake oracle. No network or account effects.
pub fn check101(v:&Value)->Value{
 use tungstenite::client::IntoClientRequest;
 struct Fixture { input:std::io::Cursor<Vec<u8>> }
 impl std::io::Read for Fixture { fn read(&mut self,b:&mut [u8])->std::io::Result<usize>{std::io::Read::read(&mut self.input,b)} }
 impl std::io::Write for Fixture {
  fn write(&mut self,b:&[u8])->std::io::Result<usize>{Ok(b.len())}
  fn flush(&mut self)->std::io::Result<()>{Ok(())}
 }
 let mut request="wss://chat.signal.org/v1/websocket/".into_client_request().unwrap();
 request.headers_mut().insert("sec-websocket-key",v["key"].as_str().unwrap().parse().unwrap());
 let result=tungstenite::client(request,Fixture{input:std::io::Cursor::new(raw(v,"wire"))});
 match result { Ok((_socket,response))=>json!({"accepted":true,"status":response.status().as_u16()}),
 Err(e)=>json!({"accepted":false,"error":format!("{e}")}) }
}

// Public-fixture-only synchronous frame reader, no sockets or account effects.
pub fn check_ws_frames(v:&Value)->Value{
 struct Fixture { input:std::io::Cursor<Vec<u8>> }
 impl std::io::Read for Fixture {fn read(&mut self,b:&mut [u8])->std::io::Result<usize>{std::io::Read::read(&mut self.input,b)}}
 impl std::io::Write for Fixture {
  fn write(&mut self,b:&[u8])->std::io::Result<usize>{Ok(b.len())}
  fn flush(&mut self)->std::io::Result<()>{Ok(())}
 }
 let mut socket=tungstenite::WebSocket::from_raw_socket(Fixture{input:std::io::Cursor::new(raw(v,"wire"))},tungstenite::protocol::Role::Client,None);
 let mut messages=vec![];
 for _ in 0..1024 {
  match socket.read(){
   Ok(tungstenite::Message::Binary(b))=>messages.push(json!({"type":"binary","data":hex(&b)})),
   Ok(tungstenite::Message::Text(b))=>messages.push(json!({"type":"text","data":hex(b.as_bytes())})),
   Ok(tungstenite::Message::Ping(b))=>messages.push(json!({"type":"ping","data":hex(&b)})),
   Ok(tungstenite::Message::Pong(b))=>messages.push(json!({"type":"pong","data":hex(&b)})),
   Ok(tungstenite::Message::Close(c))=>{messages.push(match c{Some(c)=>json!({"type":"close","code":u16::from(c.code),"reason":c.reason.as_str()}),None=>json!({"type":"close","code":null,"reason":""})});return json!({"messages":messages,"closed":true});},
   Ok(_)=>{},
   Err(e)=>return json!({"messages":messages,"closed":false,"error":format!("{e}")}),
  }
 }
 json!({"messages":messages,"closed":false,"error":"Fixture message budget exceeded"})
}
