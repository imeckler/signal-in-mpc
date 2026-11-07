//! Public fixture oracle only: actual locked Prost derives/decodes wire.proto's
//! six optional fields. This is not a replacement proof reference.
use prost::Message;
use std::io::{self, BufRead};
#[derive(Clone, PartialEq, Message)]
struct WireMessage {
    #[prost(bytes="vec", optional, tag="1")]
    ratchet_key: Option<Vec<u8>>,
    #[prost(uint32, optional, tag="2")]
    counter: Option<u32>,
    #[prost(uint32, optional, tag="3")]
    previous_counter: Option<u32>,
    #[prost(bytes="vec", optional, tag="4")]
    ciphertext: Option<Vec<u8>>,
    #[prost(bytes="vec", optional, tag="5")]
    pq_ratchet: Option<Vec<u8>>,
    #[prost(bytes="vec", optional, tag="6")]
    addresses: Option<Vec<u8>>,
}
fn hex(x: Option<Vec<u8>>) -> String {
    match x { None => "-".to_owned(), Some(x) => x.iter().map(|b| format!("{b:02x}")).collect() }
}
fn scalar(x: Option<u32>) -> String { x.map(|n| n.to_string()).unwrap_or("-".to_owned()) }
fn main() {
    for line in io::stdin().lock().lines() {
        let line = line.unwrap();
        let bytes: Vec<u8> = line.as_bytes().chunks(2).map(|s| u8::from_str_radix(std::str::from_utf8(s).unwrap(),16).unwrap()).collect();
        match WireMessage::decode(bytes.as_slice()) {
            Err(_) => println!("err"),
            Ok(x) => println!("ok|{}|{}|{}|{}|{}|{}",hex(x.ratchet_key),scalar(x.counter),scalar(x.previous_counter),hex(x.ciphertext),hex(x.pq_ratchet),hex(x.addresses)),
        }
    }
}
