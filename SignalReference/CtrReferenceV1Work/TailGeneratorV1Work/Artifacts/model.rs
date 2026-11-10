#![register_tool(charon)]
#![feature(register_tool)]
pub type Block=[u8;16];
pub struct Backend { pub counter:u32, pub nonce:[u32;4], pub keys:[u64;120] }
impl Backend {
 #[charon::opaque]
 pub fn gen_ks_block(&mut self,_block:&mut Block) { panic!("actual-source linkage") }
    pub fn gen_tail_blocks(&mut self, blocks: &mut [Block]) {
        assert!(blocks.len() < 4);
        for block in blocks {
            self.gen_ks_block(block);
        }
    }
}
