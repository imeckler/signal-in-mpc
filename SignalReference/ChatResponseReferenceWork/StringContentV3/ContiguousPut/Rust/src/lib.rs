// Exact pinned Vec.put body with concrete contiguous Take<&mut &[u8]> input.
use bytes::Buf;
pub fn put_contiguous(value:&mut Vec<u8>,input:&mut &[u8],limit:usize) {
    let mut src = input.take(limit);

        // In case the src isn't contiguous, reserve upfront.
        value.reserve(src.remaining());

        while src.has_remaining() {
            let s = src.chunk();
            let l = s.len();
            value.extend_from_slice(s);
            src.advance(l);
        }
    }

pub fn put_contiguous_one_step(value:&mut Vec<u8>,input:&mut &[u8],limit:usize) {
    let mut src=input.take(limit);

        // In case the src isn't contiguous, reserve upfront.
        value.reserve(src.remaining());

        if src.has_remaining() {
            let s = src.chunk();
            let l = s.len();
            value.extend_from_slice(s);
            src.advance(l);
        assert!(!src.has_remaining());
        }
    }
