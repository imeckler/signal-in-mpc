// Exact core mem::forget body specialized to the actual guard shape.
use std::mem::ManuallyDrop;
struct Guard<'a>(&'a mut Vec<u8>);
impl Drop for Guard<'_> { fn drop(&mut self) { self.0.clear(); } }
fn specialized(t: Guard<'_>) { let _ = ManuallyDrop::new(t); }
fn main() {
    let mut count=0;
    for length in 0..=512 {
        let data:Vec<u8>=(0..length).map(|i| ((i*73+length*17)%256) as u8).collect();
        let mut original=data.clone(); let mut replay=data.clone(); let mut dropped=data.clone();
        std::mem::forget(Guard(&mut original)); specialized(Guard(&mut replay));
        drop(Guard(&mut dropped));
        assert_eq!(original,data); assert_eq!(replay,data); assert!(dropped.is_empty()); count+=1;
    }
    println!("Compared {count} actual generic/specialized forget outcomes and actual cleanup effects");
}
