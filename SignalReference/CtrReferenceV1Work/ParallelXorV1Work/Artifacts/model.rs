pub type Batch=[[u8;16];4];
pub struct InOut<'i,'o> { pub input:&'i Batch, pub output:&'o mut Batch }
impl InOut<'_,'_> {
    pub fn xor_in2out(&mut self, data: &Batch) {
        unsafe {
            let input = *self.input;
            let mut temp = Batch::default();
            for i in 0..4 {
                for j in 0..16 {
                    temp[i][j] = input[i][j] ^ data[i][j];
                }
            }
            *self.output = temp;
        }
    }
}
