// Synthetic translator regression only. Not Signal implementation code.
pub fn apply<F: FnOnce() -> u32>(f: F) -> u32 { f() }
pub fn seven() -> u32 { 7 }
pub fn default_item() -> u32 { apply(u32::default) }
pub fn literal_item() -> u32 { apply(seven) }
pub fn apply_one<F: FnOnce(u32) -> u32>(f: F, value: u32) -> u32 { f(value) }
pub fn identity(value: u32) -> u32 { value }
pub fn pure_argument_item(value: u32) -> u32 { apply_one(identity, value) }
pub fn function_pointer(f: fn() -> u32) -> u32 { f() }
