pub trait Buf { fn remaining(&self) -> usize; }
pub struct Take<T>(pub T);
impl<T: Buf> Buf for Take<T> { fn remaining(&self) -> usize { self.0.remaining() } }
impl<T: Buf> Buf for &mut T { fn remaining(&self) -> usize { (**self).remaining() } }
pub trait Adapter { fn replace_with<B: Buf>(&mut self, input: B); }
pub fn merge<A: Adapter, B: Buf>(value: &mut A, input: &mut B) {
    value.replace_with(Take(input));
}
pub struct Value(pub usize);
impl Adapter for Value {
    fn replace_with<B: Buf>(&mut self, input: B) { self.0 = input.remaining(); }
}
pub fn entry<B: Buf>(input: &mut B) -> usize {
    let mut value = Value(0);
    merge(&mut value,input);
    value.0
}
pub fn free<B: Buf>(input: B) -> usize { input.remaining() }
pub fn free_entry<B: Buf>(input: &mut B) -> usize { free(Take(input)) }
pub fn mixed<A: Adapter,B: Buf>(value:&mut A,input:&mut B) {
    let mut closed=Value(0);merge(&mut closed,input);merge(value,input);
}
