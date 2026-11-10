    fn call<B: StreamCipherBackend<BlockSize = BS>>(self, backend: &mut B) {
        if B::ParBlocksSize::USIZE > 1 {
            let (chunks, mut tail) = self.blocks.into_chunks::<B::ParBlocksSize>();
            for mut chunk in chunks {
                let mut tmp = Default::default();
                backend.gen_par_ks_blocks(&mut tmp);
                chunk.xor_in2out(&tmp);
            }
            let n = tail.len();
            let mut buf = Array::<_, B::ParBlocksSize>::default();
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