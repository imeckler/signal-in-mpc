//! TRUSTED fixed library/dispatch content abstraction, not an AES implementation.
//! Input is the observed pre-write content; output is the complete writeback owner.
//! For this caller aliasing is abstracted by its only input read preceding its only output write.
pub type Block = [u8; 16];
pub type BatchBlocks = [Block; 4];
pub struct Cipher { pub keys: [u64; 120] }
pub struct Backend<'a>(pub &'a Cipher);
pub struct InOut<'inp, 'out, T> { pub input: &'inp T, pub output: &'out mut T }
impl<'inp, 'out, T: Copy> InOut<'inp, 'out, T> {
    pub fn clone_in(&self) -> T { *self.input }
    pub fn get_in(&self) -> &T { self.input }
    pub fn get_out(&mut self) -> &mut T { self.output }
}
// Opaque linkage slot: bound in Lean to the ACTUAL translated pinned aes256_encrypt.
// Its Rust body is never interpreted as encryption correctness.
pub fn aes256_encrypt(_keys: &[u64; 120], _blocks: &BatchBlocks) -> BatchBlocks {
    panic!("reference linkage slot must not execute")
}
