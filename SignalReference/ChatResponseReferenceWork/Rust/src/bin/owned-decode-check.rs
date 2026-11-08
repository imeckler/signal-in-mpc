use chat_response_reference::{chat_websocket::WebSocketMessage, owned_slice_replay};
use prost::Message;

fn check(input: &[u8], counts: &mut [usize; 3]) {
    let original = WebSocketMessage::decode(input);
    let replayed = owned_slice_replay::decode_slice(input);
    counts[0] += 1;
    match (original, replayed) {
        (Ok(left), Ok(right)) => { assert_eq!(left, right, "input {input:02x?}"); counts[1] += 1; }
        (Err(left), Err(right)) => { assert_eq!(format!("{left:?}"), format!("{right:?}"), "input {input:02x?}"); counts[2] += 1; }
        (left, right) => panic!("outcome mismatch input {input:02x?}: {left:?} versus {right:?}"),
    }
}
fn varint(mut value: u64) -> Vec<u8> {
    let mut out = Vec::new();
    loop {
        let byte = (value & 127) as u8; value >>= 7;
        out.push(byte | if value == 0 { 0 } else { 128 });
        if value == 0 { return out; }
    }
}
fn response(inner: &[u8]) -> Vec<u8> {
    let mut out = vec![8, 2, 26]; out.extend(varint(inner.len() as u64)); out.extend(inner); out
}
fn main() {
    let mut counts = [0; 3];
    check(&[], &mut counts);
    for a in 0..=255u8 {
        check(&[a], &mut counts);
        for b in 0..=255u8 { check(&[a,b], &mut counts); }
    }
    for inner in [vec![], vec![8,0], vec![8,1,16,200,1], vec![26,1,255],
        vec![26,2,192,128], vec![26,3,237,160,128], vec![26,4,244,144,128,128],
        vec![42,4,b'a',b':',13,10], vec![8,128], vec![34,2,0], vec![34,0,34,2,1,2]] {
        let wire = response(&inner); check(&wire, &mut counts);
        for end in 0..wire.len() { check(&wire[..end], &mut counts); }
    }
    let mut merged = response(&[8,255,255,255,255,255,255,255,255,255,1]);
    merged.extend(response(&[16,200,1,26,2,0xc2,0xa0,34,0]));
    check(&merged, &mut counts);
    for depth in [1,99,100,101] {
        let mut wire = vec![0x9b,6].repeat(depth);
        wire.extend(vec![0x9c,6].repeat(depth)); check(&wire, &mut counts);
    }
    let mut seed = 0x7d91e2a635b8c409u64;
    for size in 0..=512 {
        let mut wire = Vec::new();
        for _ in 0..size { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; wire.push(seed as u8); }
        check(&wire, &mut counts);
    }
    println!("Compared {} actual original/specialized outcomes: {} full records, {} exact Debug errors", counts[0], counts[1], counts[2]);
}
