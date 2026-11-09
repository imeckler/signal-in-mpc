// PUBLIC-FIXTURE-only actual library observations; no cryptographic correctness assumption.
use hybrid_array::{Array, typenum::{U4,U16}};
use inout::InOut;
type Block=Array<u8,U16>;
type Batch=Array<Block,U4>;
fn main() {
    let mut observations=0usize;
    for case in 0..256usize {
        let input: Block=core::array::from_fn::<_,16,_>(|i| (case.wrapping_mul(17)+i*31)as u8).into();
        let fresh: Block=core::array::from_fn::<_,16,_>(|i| (case.wrapping_mul(43)+i*7+1)as u8).into();
        let old: Block=core::array::from_fn::<_,16,_>(|i| (case+i*11+2)as u8).into();
        let mut target=old;
        {
            let mut io:InOut<'_,'_,Block>=(&input,&mut target).into();
            assert_eq!(io.clone_in(),input); observations+=1;
            *io.get_out()=fresh;
        }
        assert_eq!(target,fresh); observations+=1;
        let mut alias=input;
        {
            let mut io:InOut<'_,'_,Block>=(&mut alias).into();
            assert_eq!(io.clone_in(),input); observations+=1;
            *io.get_out()=fresh;
        }
        assert_eq!(alias,fresh); observations+=1;
        let mut batch=Batch::default();
        assert!(batch.iter().all(|b|b.iter().all(|byte|*byte==0)));observations+=1;
        batch[0]=input;
        assert_eq!(batch[0],input);observations+=1;
        assert!(batch[1..].iter().all(|b|b.iter().all(|byte|*byte==0)));observations+=1;
        let original=batch;
        let next:Batch=[fresh;4].into();
        let mut output=Batch::default();
        {
            let mut io:InOut<'_,'_,Batch>=(&batch,&mut output).into();
            assert_eq!(*io.get_in(),original);observations+=1;
            *io.get_out()=next;
        }
        assert_eq!(batch,original);observations+=1;
        assert_eq!(output,next);observations+=1;
    }
    println!("{{\"passed\":true,\"public_cases\":256,\"observations\":{observations}}}");
}
