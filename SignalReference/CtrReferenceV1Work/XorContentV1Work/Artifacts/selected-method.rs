    pub fn xor_in2out(&mut self, data: &Array<u8, N>) {
        unsafe {
            let input = ptr::read(self.in_ptr);
            let mut temp = Array::<u8, N>::default();
            for i in 0..N::USIZE {
                temp[i] = input[i] ^ data[i];
            }
            ptr::write(self.out_ptr, temp);
        }
    }