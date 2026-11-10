    fn call<B: StreamCipherBackend<BlockSize = BS>>(mut self, backend: &mut B) {
        let mut t = Default::default();
        backend.gen_ks_block(&mut t);
        self.block.xor_in2out(&t);
    }