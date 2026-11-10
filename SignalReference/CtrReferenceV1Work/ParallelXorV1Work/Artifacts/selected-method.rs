    pub fn xor_in2out(&mut self, data: &Array<Array<u8, N>, M>) {
        unsafe {
            let input = ptr::read(self.in_ptr);
            let mut temp = Array::<Array<u8, N>, M>::default();
            for i in 0..M::USIZE {
                for j in 0..N::USIZE {
                    temp[i][j] = input[i][j] ^ data[i][j];
                }
            }
            ptr::write(self.out_ptr, temp);
        }
    }