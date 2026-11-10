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
impl Backend<'_> {
            pub fn encrypt_block(&self, mut block: InOut<'_, '_, Block>) {
                let mut blocks = BatchBlocks::default();
                blocks[0] = block.clone_in().into();
                let res = aes256_encrypt(&self.0.keys, &blocks);
                *block.get_out() = res[0].into();
            }
            pub fn encrypt_par_blocks(&self, mut blocks: InOut<'_, '_, BatchBlocks>) {
                let res = aes256_encrypt(&self.0.keys, blocks.get_in());
                *blocks.get_out() = res;
            }
}

pub fn make_inout<'i,'o,T>(pair: (&'i T,&'o mut T)) -> InOut<'i,'o,T> {
 InOut { input:pair.0, output:pair.1 }
}
pub struct Nonce { pub ctr:u32, pub nonce:[u32;4] }
// Opaque selected flavor slot, bound to unchanged translated Ctr32BE<U16>::next_block.
pub fn next_block(_state:&mut Nonce)->Block { panic!("reference linkage slot") }
pub struct CtrBackend<'a,'b> { pub ctr_nonce:&'a mut Nonce, pub backend:&'b Backend<'b> }
impl CtrBackend<'_,'_> {
    pub fn gen_ks_block(&mut self, block: &mut Block) {
        let tmp = next_block(self.ctr_nonce);
        self.backend.encrypt_block(make_inout((&tmp, block)));
    }
}

impl CtrBackend<'_,'_> {
    pub fn gen_par_ks_blocks(&mut self, blocks: &mut BatchBlocks) {
        let mut tmp = BatchBlocks::default();
        for block in tmp.iter_mut() {
            *block = next_block(self.ctr_nonce);
        }
        self.backend.encrypt_par_blocks(make_inout((&tmp, blocks)));
    }
}
