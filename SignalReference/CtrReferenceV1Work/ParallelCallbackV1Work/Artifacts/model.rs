#![register_tool(charon)]
#![feature(register_tool)]
pub type Batch=[[u8;16];4];
pub struct Backend {pub counter:u32,pub nonce:[u32;4],pub keys:[u64;120]}
pub struct InOut<'i,'o> {pub input:&'i Batch,pub output:&'o mut Batch}
impl Backend { #[charon::opaque] pub fn gen_par_ks_blocks(&mut self,_out:&mut Batch) {panic!("actual source linkage")}}
impl InOut<'_,'_> { #[charon::opaque] pub fn xor_in2out(&mut self,_data:&Batch) {panic!("actual source linkage")}}
pub fn apply_parallel_chunk(backend:&mut Backend,mut chunk:InOut<'_,'_>) {
                let mut tmp = Default::default();
                backend.gen_par_ks_blocks(&mut tmp);
                chunk.xor_in2out(&tmp);
            }
