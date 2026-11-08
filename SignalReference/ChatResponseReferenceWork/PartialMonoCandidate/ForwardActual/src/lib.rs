/// Extraction root only: calls the pinned actual &mut T Buf implementation.
pub fn forward_actual<B:bytes::Buf>(mut input:&mut B,n:usize) {
    bytes::Buf::advance(&mut input,n)
}
