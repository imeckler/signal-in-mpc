#[path="../../Rust/src/lib.rs"] mod original;
mod schema { include!(concat!(env!("OUT_DIR"), "/signal.proto.chat_websocket.rs")); }
use prost::encoding::{DecodeContext,WireType,message};
fn main() {
    let payloads:Vec<Vec<u8>>=vec![vec![],vec![8,1],vec![8,1,8,2],vec![16,200,1],vec![26,1,255],vec![26,2,0xc3,0xa9],vec![34,2,0,255],vec![42,3,b'a',b':',b'b'],vec![48,1],vec![0],vec![11,12],vec![11,20]];
    let tails=vec![vec![],vec![8,2],vec![255,255,255]];
    let wires=[WireType::Varint,WireType::SixtyFourBit,WireType::LengthDelimited,WireType::StartGroup,WireType::EndGroup,WireType::ThirtyTwoBit];
    let filled=schema::WebSocketResponseMessage { id:Some(99),status:Some(200),message:Some("old".into()),body:Some(bytes::Bytes::from_static(b"old")),headers:vec!["x: old".into()] };
    let mut count=0;
    for initial in [schema::WebSocketResponseMessage::default(),filled] {
        for length in 0..=24 {
            for payload in &payloads { for tail in &tails { for wire in wires {
                let mut input=vec![length];input.extend(payload);input.extend(tail);
                let (mut a,mut b)=(initial.clone(),initial.clone());
                let (mut sa,mut sb)=(input.as_slice(),input.as_slice());
                let ra=message::merge(wire,&mut a,&mut sa,DecodeContext::default()).map_err(|e|e.to_string());
                let rb=original::merge_submessage(wire,&mut b,&mut sb,DecodeContext::default()).map_err(|e|e.to_string());
                assert_eq!((ra,a,sa),(rb,b,sb));count+=1;
            } } }
        }
    }
    let mut state=schema::WebSocketResponseMessage::default();
    let mut input=&[1,8,1,8,2][..];
    let error=message::merge(WireType::LengthDelimited,&mut state,&mut input,DecodeContext::default()).unwrap_err();
    assert!(error.to_string().contains("delimited length exceeded"),"{error}");
    assert_eq!(state.id,Some(1));assert_eq!(input,&[8,2]);
    println!("{count} exact original/wrapper result+mutation+suffix comparisons PASS; parent-tail overrun observed");
}
