fn requires_static(_: &'static str) {}
fn dynamic_is_rejected(value: &str) { requires_static(value); }
