#![register_tool(charon)]
#![feature(register_tool)]
pub struct ReadBuffer { pub buffer:[u8;16] }
impl ReadBuffer {
    pub fn write_block(
        &mut self,
        read_len: usize,
        gen_block: impl FnOnce(&mut [u8;16]),
        read_fn: impl FnOnce(&[u8]),
    ) {
        if read_len == 0 {
            return;
        }
        assert!(read_len < 16);

        let g = ResetGuard(self);
        let buf = &mut g.0.buffer;

        // Note that generated block is likely to break the `ReadBuffer` invariant.
        // We restore it using `set_pos_unchecked` below and in case if one of the closures
        // panic the buffer gets reset by the guard.
        gen_block(buf);
        read_fn(&buf[..read_len]);

        core::mem::forget(g);

        // We checked that `read_len` satisfies the `set_pos_unchecked` safety contract
        unsafe { self.set_pos_unchecked(read_len) };
    }
    unsafe fn set_pos_unchecked(&mut self, pos: usize) {
        debug_assert!(pos != 0 && pos <= 16);
        self.buffer[0] = pos as u8;
    }
    pub fn reset(&mut self) {
        self.buffer[0] = 16;
    }
}
struct ResetGuard<'a>(&'a mut ReadBuffer);
impl Drop for ResetGuard<'_> { fn drop(&mut self) { self.0.reset(); } }
