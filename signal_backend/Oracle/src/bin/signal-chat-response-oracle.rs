// PUBLIC FIXTURES ONLY, separate binary from the running native crypto oracle.
// Uses actual generated pinned prost decoder. The non-public libsignal net
// response validation below is copied from inspected chat/ws.rs and chat.rs;
// this is NOT a call to that private target conversion API.
use std::io::{self,BufRead};
use prost::Message;
use serde_json::{json,Value};
use tungstenite::http::{HeaderMap,HeaderName,HeaderValue,StatusCode};
mod proto{include!(concat!(env!("OUT_DIR"),"/signal.proto.chat_websocket.rs"));}
fn raw(s:&str)->Result<Vec<u8>,String>{if s.len()%2!=0{return Err("odd hex".into())}(0..s.len()).step_by(2).map(|i|u8::from_str_radix(&s[i..i+2],16).map_err(|e|e.to_string())).collect()}
fn hex(x:&[u8])->String{x.iter().map(|b|format!("{b:02x}")).collect()}
fn check(v:&Value)->Result<Value,String>{
 let data=raw(v["wire"].as_str().ok_or("missing hex wire")?)?;
 let message=proto::WebSocketMessage::decode(data.as_slice()).map_err(|e|format!("protobuf:{e}"))?;
 if message.r#type.unwrap_or_default()!=2{return Err("not RESPONSE".into())}
 if message.request.is_some(){return Err("response has request".into())}
 let response=message.response.ok_or("missing response")?;
 let id=response.id.ok_or("missing id")?;
 let n:u16=response.status.unwrap_or_default().try_into().map_err(|_|"status exceeds u16")?;
 let status=StatusCode::from_u16(n).map_err(|_|"invalid HTTP status")?;
 let mut headers=HeaderMap::new();
 for header in response.headers {
  let(name,value)=header.split_once(':').ok_or("header missing colon")?;
  let name=HeaderName::try_from(name).map_err(|_|"invalid header name")?;
  let value=HeaderValue::from_str(value.trim()).map_err(|_|"invalid header value")?;
  headers.append(name,value);
 }
 let expected=v.get("expected_id").and_then(Value::as_u64);
 let correlated=expected.map(|expected|expected==id);
 Ok(json!({"accepted":true,"id":id,"status":status.as_u16(),"is_success":status.is_success(),
  "correlated":correlated,"body_present":response.body.is_some(),"body":hex(response.body.as_deref().unwrap_or_default()),
  "message_present":response.message.is_some(),"message_hex":hex(response.message.as_deref().unwrap_or_default().as_bytes()),"header_count":headers.len(),
  "boundary":"actual generated prost; copied inspected private validation"}))
}
fn main(){for line in io::stdin().lock().lines(){
 let output=match line.map_err(|e|e.to_string()).and_then(|s|serde_json::from_str::<Value>(&s).map_err(|e|e.to_string())).and_then(|v|check(&v)){
  Ok(value)=>value,Err(error)=>json!({"accepted":false,"error":error})};println!("{output}");
}}
