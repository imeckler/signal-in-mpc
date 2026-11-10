// PUBLIC disposable fixtures only: exercise the unchanged pinned library.
use block_buffer::{ReadBuffer,array::typenum::U16};
use std::panic::{catch_unwind,AssertUnwindSafe};
fn main() {
 std::panic::set_hook(Box::new(|_| {}));
 let mut observations=0usize;
 for seed in 0..64usize {
  let bytes: [u8;16]=core::array::from_fn(|i| (seed*37+i*13) as u8);
  for n in 0..16usize {
   let mut b=ReadBuffer::<U16>::default();
   let mut generated=false;let mut read=false;
   b.write_block(n, |out| {generated=true;out.copy_from_slice(&bytes)}, |s| {read=true;assert_eq!(s,&bytes[..n]);});
   assert_eq!(generated,n!=0);assert_eq!(read,n!=0);observations+=2;
   if n==0 {assert_eq!(b.remaining(),0);observations+=1;}
   else {assert_eq!(b.remaining(),16-n);assert_eq!(b.read_cached(usize::MAX),&bytes[n..]);assert_eq!(b.remaining(),0);observations+=3;}
  }
  for n in 1..16usize {
   for stage in 0..2 {
    let mut b=ReadBuffer::<U16>::default();
    let result=catch_unwind(AssertUnwindSafe(|| b.write_block(n, |out| {
      out.copy_from_slice(&bytes);if stage==0 {panic!("fixture generator failure")}
     }, |_| {if stage==1 {panic!("fixture reader failure")}})));
    assert!(result.is_err());assert_eq!(b.remaining(),0);assert!(b.read_cached(99).is_empty());observations+=3;
   }
  }
  for n in [16usize,17,usize::MAX] {
   let mut b=ReadBuffer::<U16>::default();b.write_block(7,|out|out.copy_from_slice(&bytes), |_|{});
   let result=catch_unwind(AssertUnwindSafe(|| b.write_block(n, |_|panic!("must not generate"), |_|panic!("must not read"))));
   assert!(result.is_err());assert_eq!(b.remaining(),9);assert_eq!(b.read_cached(99),&bytes[7..]);observations+=3;
  }
 }
 println!("{{\"passed\":true,\"public_seeds\":64,\"observations\":{observations}}}");
}
