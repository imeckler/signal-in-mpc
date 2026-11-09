pub struct ReadBuffer { pub buffer:[u8;16] }
impl ReadBuffer {
    pub fn get_pos(&self) -> usize {
        let pos = self.buffer[0];
        if pos == 0 || pos > 16 {
            debug_assert!(false);
            // SAFETY: `pos` never breaks the invariant
            unsafe {
                core::hint::unreachable_unchecked();
            }
        }
        pos as usize
    }
    pub fn size(&self) -> usize {
        16
    }
    pub fn remaining(&self) -> usize {
        self.size() - self.get_pos()
    }
    unsafe fn set_pos_unchecked(&mut self, pos: usize) {
        debug_assert!(pos != 0 && pos <= 16);
        self.buffer[0] = pos as u8;
    }
    pub fn read_cached(&mut self, len: usize) -> &[u8] {
        let rem = self.remaining();
        let new_len = core::cmp::min(rem, len);
        let pos = self.get_pos();

        // SAFETY: `pos + new_len` is not equal to zero and not bigger than block size
        unsafe { self.set_pos_unchecked(pos + new_len) };
        &self.buffer[pos..][..new_len]
    }
    pub fn reset(&mut self) {
        self.buffer[0] = 16;
    }
}
