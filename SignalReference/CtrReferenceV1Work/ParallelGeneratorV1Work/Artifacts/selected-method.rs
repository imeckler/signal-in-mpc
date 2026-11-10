    fn gen_par_ks_blocks(&mut self, blocks: &mut ParBlocks<Self>) {
        let mut tmp = ParBlocks::<Self>::default();
        for block in tmp.iter_mut() {
            *block = F::next_block(self.ctr_nonce);
        }
        self.backend.encrypt_par_blocks((&tmp, blocks).into());
    }