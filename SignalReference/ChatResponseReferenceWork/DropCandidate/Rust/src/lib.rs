//! Regression: error-time mutation must survive precise destructor translation.
struct ClearGuard<'a>(&'a mut u8);
impl Drop for ClearGuard<'_> {
    fn drop(&mut self) { *self.0 = 0; }
}
pub fn guarded(value: &mut u8, success: bool) -> Result<(), ()> {
    let guard = ClearGuard(value);
    if success { core::mem::forget(guard); Ok(()) } else { Err(()) }
}
pub fn always_error(value: &mut u8) -> Result<(), ()> {
    let _guard = ClearGuard(value);
    Err(())
}
