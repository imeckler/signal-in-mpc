#[path="Rust/src/lib.rs"] mod original;
fn main() {
    let mut cases = 0;
    for left in 0..64 {
        for right in 0..64 {
            let (mut a, mut b) = (left,right);
            assert_eq!((original::actual(&mut a,&mut b),a,b),(42,7,9));
            let (mut a,mut b,mut closure_state) = (left,right,0);
            let result = original::invoke(|x,y,n| {
                closure_state = n; *x = n; *y = 9; 42
            }, &mut a,&mut b);
            assert_eq!((result,a,b,closure_state),(42,7,9,7));
            cases += 2;
        }
    }
    println!("{cases} native output/borrow/closure-restoration cases PASS");
}
