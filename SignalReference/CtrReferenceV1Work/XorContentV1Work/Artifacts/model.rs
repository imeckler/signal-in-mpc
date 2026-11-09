pub type Block=[u8;16];
pub struct InOut<'i,'o> { pub input:&'i Block, pub output:&'o mut Block }
impl InOut<'_,'_> {
    pub fn xor_in2out(&mut self, data: &Block) {
        unsafe {
            let input = *self.input;
            let mut temp = Block::default();
            for i in 0..16 {
                temp[i] = input[i] ^ data[i];
            }
            *self.output = temp;
        }
    }
}
