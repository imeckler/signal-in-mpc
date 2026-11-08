use borrow_clause_regression::{Adapter,Buf,Take,Value,entry};
struct Count(usize);
impl Buf for Count { fn remaining(&self)->usize { self.0 } }
// Typed Rust counterpart of the LLBC closed-dictionary substitution: actual
// Adapter impl, unchanged method body, same borrowed input lifetime.
fn specialized(input:&mut Count)->usize {
    let mut value=Value(0);
    <Value as Adapter>::replace_with(&mut value,Take(input));
    value.0
}
fn main() {
    for n in 0..=4096 {
        let mut a=Count(n);let mut b=Count(n);
        let x=entry(&mut a);let y=specialized(&mut b);
        assert_eq!((x,a.0),(n,n));assert_eq!((y,b.0),(x,a.0));
    }
    println!("Compared 4097 actual generic/closed-impl results and exact borrowed inputs");
}
