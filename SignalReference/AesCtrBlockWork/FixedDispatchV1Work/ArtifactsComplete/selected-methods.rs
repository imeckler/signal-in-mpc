            fn encrypt_block(&self, mut block: InOut<'_, '_, Block>) {
                let mut blocks = BatchBlocks::default();
                blocks[0] = block.clone_in().into();
                let res = $fixslice_encrypt(&self.0.keys, &blocks);
                *block.get_out() = res[0].into();
            }

            #[inline(always)]
            fn encrypt_par_blocks(&self, mut blocks: InOut<'_, '_, BatchBlocks>) {
                let res = $fixslice_encrypt(&self.0.keys, blocks.get_in());
                *blocks.get_out() = res;
            }