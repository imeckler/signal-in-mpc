            for mut chunk in chunks {
                let mut tmp = Default::default();
                backend.gen_par_ks_blocks(&mut tmp);
                chunk.xor_in2out(&tmp);
            }