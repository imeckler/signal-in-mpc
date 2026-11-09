pub fn invoke<F: FnMut(&mut u32, &mut u32, u32) -> u32>(
    mut callback: F, left: &mut u32, right: &mut u32,
) -> u32 { callback(left, right, 7) }
pub fn actual(left: &mut u32, right: &mut u32) -> u32 {
    invoke(|a, b, n| { *a = n; *b = 9; 42 }, left, right)
}
