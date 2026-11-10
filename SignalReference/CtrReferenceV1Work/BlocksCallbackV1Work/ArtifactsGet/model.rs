#![register_tool(charon)]
#![feature(register_tool)]
pub type Block=[u8;16];pub type Batch=[Block;4];
pub struct InOut<T> {pub input:T,pub output:T}
impl InOut<Block> {#[charon::opaque] pub fn xor_in2out(&mut self,_data:&Block){panic!("actual source linkage")}}
impl InOut<Batch> {#[charon::opaque] pub fn xor_in2out(&mut self,_data:&Batch){panic!("actual source linkage")}}
pub struct Backend {pub counter:u32,pub nonce:[u32;4],pub keys:[u64;120]}
impl Backend {
 #[charon::opaque] pub fn gen_ks_block(&mut self,_out:&mut Block){panic!("actual source linkage")}
 #[charon::opaque] pub fn gen_par_ks_blocks(&mut self,_out:&mut Batch){panic!("actual source linkage")}
 #[charon::opaque] pub fn gen_tail_blocks(&mut self,_out:&mut[Block]){panic!("actual source linkage")}
}
// TRUSTED coherent prechunked content view; no crypto computation here.
pub struct InOutBuf<'a> {pub chunks:&'a mut[InOut<Batch>],pub tail:&'a mut[InOut<Block>]}
pub struct Tail<'a> {pub elements:&'a mut[InOut<Block>]}
impl<'a> InOutBuf<'a> {
 pub fn into_chunks(self)->(&'a mut[InOut<Batch>],Tail<'a>){(self.chunks,Tail{elements:self.tail})}
}
impl Tail<'_> {
 pub fn len(&self)->usize{self.elements.len()}
 #[charon::opaque]
 pub fn get(&mut self,i:usize)->&mut InOut<Block>{&mut self.elements[i]}
}
// Fixed parallel-size4 eliminates this source branch. Fail closed if reached.
impl<'a> IntoIterator for InOutBuf<'a> {
 type Item=&'a mut InOut<Block>;type IntoIter=core::slice::IterMut<'a,InOut<Block>>;
 fn into_iter(self)->Self::IntoIter{panic!("unreachable fixed-parallel4 branch")}
}
pub struct ApplyBlocksCtx<'a> {pub blocks:InOutBuf<'a>}
impl ApplyBlocksCtx<'_> {
 #[allow(unused_mut)]
 pub fn call(self,backend:&mut Backend) {
        if 4 > 1 {
            let (chunks, mut tail) = self.blocks.into_chunks();
            for mut chunk in chunks {
                let mut tmp = Default::default();
                backend.gen_par_ks_blocks(&mut tmp);
                chunk.xor_in2out(&tmp);
            }
            let n = tail.len();
            let mut buf = Batch::default();
            let ks = &mut buf[..n];
            backend.gen_tail_blocks(ks);
            for i in 0..n {
                tail.get(i).xor_in2out(&ks[i]);
            }
        } else {
            for mut block in self.blocks {
                let mut t = Default::default();
                backend.gen_ks_block(&mut t);
                block.xor_in2out(&t);
            }
        }
    }
}
