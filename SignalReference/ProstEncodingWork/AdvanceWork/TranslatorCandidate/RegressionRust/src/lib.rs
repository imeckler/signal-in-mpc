//! Translator regressions only. This is not a libsignal reference model.

pub trait Stops {
    fn stop(self) -> !;
}

pub fn call<T: Stops>(value: T) -> u8 {
    value.stop()
}

pub fn guarded<T: Stops>(value: T, proceed: bool) -> u8 {
    if proceed {
        7
    } else {
        value.stop()
    }
}

pub fn panic_stop() -> ! {
    panic!("never regression")
}

pub fn panic_caller() -> u8 {
    panic_stop()
}

pub fn spin_stop() -> ! {
    loop {}
}

pub fn spin_caller() -> u8 {
    spin_stop()
}
