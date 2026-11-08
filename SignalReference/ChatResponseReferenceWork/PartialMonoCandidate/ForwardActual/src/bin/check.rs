use actual_buf_forward_reference::forward_actual;
use bytes::{Buf,Bytes};
use std::panic::{catch_unwind,AssertUnwindSafe};
fn error(x:Box<dyn std::any::Any+Send>)->String {
    if let Some(s)=x.downcast_ref::<String>() { s.clone() }
    else if let Some(s)=x.downcast_ref::<&str>() { s.to_string() }
    else { "non-string panic".into() }
}
fn outcome<B:Buf>(input:&mut B,n:usize,wrapped:bool)->Result<(),String> {
    catch_unwind(AssertUnwindSafe(|| {
        if wrapped {forward_actual(input,n)} else {B::advance(input,n)}
    })).map_err(error)
}
fn main() {
    std::panic::set_hook(Box::new(|_|{}));
    let (mut cases,mut panics)=(0,0);
    for len in 0..=32 {
        let data:Vec<u8>=(0..len).map(|n|(n*73+len) as u8).collect();
        for n in 0..=len+1 {
            let mut a=data.as_slice();let mut b=data.as_slice();
            let x=outcome(&mut a,n,true);let y=outcome(&mut b,n,false);
            assert_eq!(x,y);assert_eq!(a,b);panics+=usize::from(x.is_err());cases+=1;
            let mut a=Bytes::copy_from_slice(&data);let mut b=a.clone();
            let x=outcome(&mut a,n,true);let y=outcome(&mut b,n,false);
            assert_eq!(x,y);assert_eq!(a,b);panics+=usize::from(x.is_err());cases+=1;
        }
    }
    println!("Compared {cases} actual/direct forwarding outcomes and exact suffixes, including {panics} exact panic payloads");
}
