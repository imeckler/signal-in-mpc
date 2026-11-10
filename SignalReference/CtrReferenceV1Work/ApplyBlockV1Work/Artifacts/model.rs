#![register_tool(charon)]
#![feature(register_tool)]
pub type Block=[u8;16];
pub struct Backend { pub counter:u32, pub nonce:[u32;4], pub keys:[u64;120] }
pub struct InOut<'i,'o> { pub input:&'i Block, pub output:&'o mut Block }
impl Backend {
 #[charon::opaque]
 pub fn gen_ks_block(&mut self,_block:&mut Block) { panic!("actual-source linkage") }
}
impl InOut<'_,'_> {
 #[charon::opaque]
 pub fn xor_in2out(&mut self,_data:&Block) { panic!("actual-source linkage") }
}
pub struct ApplyBlockCtx<'i,'o> { pub block:InOut<'i,'o> }
impl ApplyBlockCtx<'_,'_> {
    pub fn call(mut self, backend: &mut Backend) {
        let mut t = Default::default();
        backend.gen_ks_block(&mut t);
        self.block.xor_in2out(&t);
    }
}
