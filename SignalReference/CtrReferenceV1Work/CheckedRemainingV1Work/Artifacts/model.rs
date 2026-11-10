#![register_tool(charon)]
#![feature(register_tool)]
pub struct StreamCipherError;
pub struct Core {pub counter:u32}
pub struct ReadBuffer {pub buffer:[u8;16]}
pub struct Wrapper {pub core:Core,pub buffer:ReadBuffer}
impl Core { #[charon::opaque] pub fn remaining_blocks(&self)->Option<usize>{panic!("actual remaining")}}
impl ReadBuffer { #[charon::opaque] pub fn remaining(&self)->usize{panic!("actual remaining")}}
impl Wrapper {
    pub fn check_remaining(&self, data_len: usize) -> Result<(), StreamCipherError> {
        let Some(rem_blocks) = self.core.remaining_blocks() else {
            return Ok(());
        };
        let Some(data_len) = data_len.checked_sub(self.buffer.remaining()) else {
            return Ok(());
        };
        let req_blocks = data_len.div_ceil(16);
        if req_blocks > rem_blocks {
            Err(StreamCipherError)
        } else {
            Ok(())
        }
    }
}
