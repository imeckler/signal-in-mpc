use bytes::{Buf,BufMut};
use contiguous_put_reference::{put_contiguous,put_contiguous_one_step};
fn main() {
    let mut cases=0;
    for len in 0..=64 {
        let data:Vec<u8>=(0..len).map(|n|((n*73+len*11)%256) as u8).collect();
        for limit in (0..=len+2).chain(std::iter::once(usize::MAX)) {
            for old_len in [0,1,7] {
                let old:Vec<u8>=(0..old_len).map(|n| n as u8 ^ 0xa5).collect();
                let(mut a,mut b,mut c)=(old.clone(),old.clone(),old);
                let(mut x,mut y,mut z)=(data.as_slice(),data.as_slice(),data.as_slice());
                a.put((&mut x).take(limit));
                put_contiguous(&mut b,&mut y,limit);
                put_contiguous_one_step(&mut c,&mut z,limit);
                assert_eq!((&a,x),(&b,y));assert_eq!((&a,x),(&c,z));
                cases+=1;
            }
        }
    }
    println!("Compared {cases} actual/original-replay/guarded-single-body Vec results and exact suffixes");
}
