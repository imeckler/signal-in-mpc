    fn check_remaining(&self, data_len: usize) -> Result<(), StreamCipherError> {
        let Some(rem_blocks) = self.core.remaining_blocks() else {
            return Ok(());
        };
        let Some(data_len) = data_len.checked_sub(self.buffer.remaining()) else {
            return Ok(());
        };
        let req_blocks = data_len.div_ceil(T::BlockSize::USIZE);
        if req_blocks > rem_blocks {
            Err(StreamCipherError)
        } else {
            Ok(())
        }
    }