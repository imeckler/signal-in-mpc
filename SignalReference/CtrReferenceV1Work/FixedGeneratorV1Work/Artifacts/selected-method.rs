    fn gen_ks_block(&mut self, block: &mut Block<Self>) {
        let tmp = F::next_block(self.ctr_nonce);
        self.backend.encrypt_block((&tmp, block).into());
    }