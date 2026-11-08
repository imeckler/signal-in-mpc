use bytes::{Buf, Bytes};
use prost::encoding::{self, DecodeContext, WireType};
fn hex(v: &[u8]) -> String {v.iter().map(|b|format!("{b:02x}")).collect()}
fn length(n: usize) -> Vec<u8> {let mut out=Vec::new(); encoding::encode_varint(n as u64,&mut out);out}
fn main(){
 std::panic::set_hook(Box::new(|_|{}));
 for n in (0..=65).chain([127,128,255,256,511,512]) {
  let data:Vec<u8>=(0..n).map(|i|((i*37+n*11)%256)as u8).collect();
  for count in (0..=n+1).step_by(if n>65 {17}else{1}).chain([n,n+1]) {
   let mut slice=data.as_slice();
   let a=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||slice.copy_to_bytes(count)));
   println!("COPY slice {n} {count} {} {} {}",a.is_ok(),a.as_ref().map(|x|hex(x)).unwrap_or("-".into()),hex(slice));
   let mut bytes=Bytes::copy_from_slice(&data);
   let b=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||bytes.copy_to_bytes(count)));
   println!("COPY bytes {n} {count} {} {} {}",b.is_ok(),b.as_ref().map(|x|hex(x)).unwrap_or("-".into()),hex(&bytes));
  }
  for declared in [0,n/2,n,n+1,n+17] {
   let mut wire=length(declared);wire.extend(&data);let mut buf=wire.as_slice();let mut value=vec![0xaa,0xbb];
   let result=encoding::bytes::merge(WireType::LengthDelimited,&mut value,&mut buf,DecodeContext::default());
   println!("MERGE {n} {declared} {} {} {}",result.is_ok(),hex(&value),hex(buf));
  }
  for final_len in [0,n/2,n] {
   let mut first=length(n);first.extend(&data);let mut buf=first.as_slice();let mut value=vec![1,2,3];
   encoding::bytes::merge(WireType::LengthDelimited,&mut value,&mut buf,DecodeContext::default()).unwrap();
   let mut second=length(final_len);second.extend(&data[..final_len]);let mut next=second.as_slice();
   encoding::bytes::merge(WireType::LengthDelimited,&mut value,&mut next,DecodeContext::default()).unwrap();
   println!("DUP {n} {final_len} {} {}",hex(&value),hex(next));
  }
 }
}
