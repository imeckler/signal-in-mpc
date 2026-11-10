    fn gen_tail_blocks(&mut self, blocks: &mut [Block<Self>]) {
        assert!(blocks.len() < Self::ParBlocksSize::USIZE);
        for block in blocks {
            self.gen_ks_block(block);
        }
    }