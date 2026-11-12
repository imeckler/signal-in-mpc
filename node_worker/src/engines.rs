//! The engines behind the C ABI (`handshake_backend/EmpHybridWork/engine_abi.h`).
//!
//! [`Engines`] is what the shell needs from them in S8: the legacy library (every operation
//! that is not the shell's), its two connection-table halves, abort, and public counters.
//! [`native::NativeEngines`] (feature `engine`) is the real one; tests use their own.
//! The engines open their own links; no function here hands them bytes to send.

#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Counters {
    pub and_gates: u64,
    pub boolean_bytes: u64,
    pub field_bytes: u64,
    pub field_products: u64,
    pub stock_minted: u64,
    pub stock_seconds: f64,
}

pub trait Engines {
    fn counters(&mut self) -> Counters;
    /// One legacy operation (engine_abi.h `ea_legacy_dispatch`), already agreed.
    fn legacy(&mut self, code: u8, sequence: u64, payload: &[u8]) -> Result<Vec<u8>, String>;
    /// Operation 90's engine half.
    fn select(&mut self, index: u8) -> Result<(), String>;
    /// Operation 91's engine half.
    fn reset(&mut self) -> Result<(), String>;
    /// Operation 8, and after any failure: drop every private TLS state.
    fn abort(&mut self);
    /// The engines' measurement rows to stderr.
    fn profile_report(&mut self, prefix: &str);
}

/// The operations the legacy library serves (the same list as `legacy_operation` in
/// legacy_abi.cpp): 1-7, 12-16, 30, 32, 33, 36-38, 40-66, 80, 81. Everything else that is not
/// the shell's own (8, 9, 10, 11, 17, 39, 90, 91, 92) is refused: the retired fixture and
/// private-profile operations 18-29, 31, 34, 35, and any unknown code.
pub fn is_legacy(code: u8) -> bool {
    matches!(code, 1..=7 | 12..=16 | 30 | 32 | 33 | 36..=38 | 40..=66 | 80 | 81)
}

#[cfg(feature = "engine")]
pub mod native {
    use super::{Counters, Engines};
    use crate::config::Config;
    use std::ffi::{CStr, CString, c_int};

    /// engine_abi.h, the part S8 uses. (The Boolean and field instruction functions are
    /// declared there and linked from S9 on, by interp.rs.)
    #[allow(non_camel_case_types, dead_code)]
    mod ffi {
        use std::ffi::{c_char, c_int, c_uint};
        #[repr(C)]
        pub struct ea_session {
            _private: [u8; 0],
        }
        #[repr(C)]
        pub struct ea_bytes {
            pub data: *mut u8,
            pub len: usize,
        }
        #[repr(C)]
        pub struct ea_config {
            pub party: c_int,
            pub port: c_uint,
            pub field_port: c_uint,
            pub peer: *const c_char,
            pub listen: *const c_char,
            pub field_peer: *const c_char,
            pub stock_factories: c_uint,
            pub stock_batch: usize,
            pub stock_reserve: usize,
            pub field_batch: c_uint,
            pub field_reserve: c_uint,
            pub field_lines: c_uint,
            pub field_direct: c_int,
            pub challenge_domain: *const c_char,
        }
        #[repr(C)]
        #[derive(Default)]
        pub struct ea_counters {
            pub and_gates: u64,
            pub boolean_bytes: u64,
            pub field_bytes: u64,
            pub field_products: u64,
            pub stock_minted: u64,
            pub stock_seconds: f64,
        }
        #[repr(C)]
        pub struct ea_legacy_config {
            pub cache_script: *const c_char,
            pub session: *const c_char,
            pub ladder_agreement: c_int,
            pub typed_open: c_int,
            pub hinted: c_int,
            pub peer_wait_seconds: c_int,
            pub require_pinned: c_int,
        }
        unsafe extern "C" {
            pub fn ea_security_mode() -> *const c_char;
            pub fn ea_test_build() -> c_int;
            pub fn ea_error_message() -> *const c_char;
            pub fn ea_bytes_free(bytes: *mut ea_bytes);
            pub fn ea_session_create(config: *const ea_config, out: *mut *mut ea_session) -> c_int;
            pub fn ea_session_destroy(session: *mut ea_session);
            pub fn ea_counters_read(session: *mut ea_session, out: *mut ea_counters) -> c_int;
            pub fn ea_profile_report(session: *mut ea_session, prefix: *const c_char) -> c_int;
            pub fn ea_legacy_open(session: *mut ea_session, config: *const ea_legacy_config) -> c_int;
            pub fn ea_legacy_dispatch(session: *mut ea_session, code: u8, sequence: u64, payload: *const u8, len: usize, out: *mut ea_bytes) -> c_int;
            pub fn ea_legacy_select(session: *mut ea_session, index: u64) -> c_int;
            pub fn ea_legacy_reset(session: *mut ea_session) -> c_int;
            pub fn ea_legacy_abort(session: *mut ea_session) -> c_int;
        }
    }

    fn last_error() -> String {
        // SAFETY: the library returns a NUL-terminated string that stays valid until the next
        // failing call on this thread; it is copied at once.
        unsafe { CStr::from_ptr(ffi::ea_error_message()).to_string_lossy().into_owned() }
    }
    fn check(status: c_int) -> Result<(), String> {
        if status == 0 { Ok(()) } else { Err(last_error()) }
    }
    fn text(s: &str) -> Result<CString, String> {
        CString::new(s).map_err(|_| "a setting contains a NUL byte".to_string())
    }

    /// "malicious-128" or "semi-honest", and whether this is the -test library.
    pub fn build_identity() -> (String, bool) {
        // SAFETY: a static NUL-terminated string.
        let mode = unsafe { CStr::from_ptr(ffi::ea_security_mode()) }.to_string_lossy().into_owned();
        (mode, unsafe { ffi::ea_test_build() } != 0)
    }

    pub struct NativeEngines {
        session: *mut ffi::ea_session,
    }

    impl NativeEngines {
        /// Starts both engines, then the legacy library (interactive: the other worker does the
        /// same at the same point).
        pub fn open(config: &Config, require_pinned: bool) -> Result<NativeEngines, String> {
            let peer = text(&config.peer.to_string())?;
            let listen = config.listen.map(|a| text(&a.to_string())).transpose()?;
            let field_peer = config.field_peer().map(|p| text(&p)).transpose()?;
            let domain = text(&config.challenge_domain())?;
            let c = ffi::ea_config {
                party: config.party as c_int,
                port: config.engine_port(),
                field_port: config.field_port(),
                peer: peer.as_ptr(),
                listen: listen.as_ref().map_or(std::ptr::null(), |l| l.as_ptr()),
                field_peer: field_peer.as_ref().map_or(std::ptr::null(), |p| p.as_ptr()),
                stock_factories: config.stock_factories,
                stock_batch: config.stock_batch as usize,
                stock_reserve: config.stock_reserve as usize,
                field_batch: config.field_batch,
                field_reserve: config.field_reserve,
                field_lines: config.field_lines,
                field_direct: config.field_direct as c_int,
                challenge_domain: domain.as_ptr(),
            };
            let mut session = std::ptr::null_mut();
            // SAFETY: every pointer in `c` refers to a CString alive for this call.
            check(unsafe { ffi::ea_session_create(&c, &mut session) })?;
            let engines = NativeEngines { session };
            let script = text(&config.cache_script)?;
            let agreed = text(&config.session)?;
            let l = ffi::ea_legacy_config {
                cache_script: script.as_ptr(),
                session: agreed.as_ptr(),
                ladder_agreement: config.ladder as c_int,
                typed_open: config.typed_open as c_int,
                hinted: config.hinted as c_int,
                peer_wait_seconds: config.peer_wait.map_or(0, |w| w.as_secs() as c_int),
                require_pinned: require_pinned as c_int,
            };
            // SAFETY: as above; the session is live.
            check(unsafe { ffi::ea_legacy_open(engines.session, &l) })?;
            Ok(engines)
        }
    }

    impl Drop for NativeEngines {
        fn drop(&mut self) {
            // SAFETY: created by ea_session_create, destroyed once.
            unsafe { ffi::ea_session_destroy(self.session) }
        }
    }

    impl Engines for NativeEngines {
        fn counters(&mut self) -> Counters {
            let mut c = ffi::ea_counters::default();
            // SAFETY: live session, valid out pointer.
            let _ = unsafe { ffi::ea_counters_read(self.session, &mut c) };
            Counters {
                and_gates: c.and_gates,
                boolean_bytes: c.boolean_bytes,
                field_bytes: c.field_bytes,
                field_products: c.field_products,
                stock_minted: c.stock_minted,
                stock_seconds: c.stock_seconds,
            }
        }
        fn legacy(&mut self, code: u8, sequence: u64, payload: &[u8]) -> Result<Vec<u8>, String> {
            let mut out = ffi::ea_bytes { data: std::ptr::null_mut(), len: 0 };
            // SAFETY: payload is a valid slice for the call; out is released below.
            let status = unsafe { ffi::ea_legacy_dispatch(self.session, code, sequence, payload.as_ptr(), payload.len(), &mut out) };
            check(status)?;
            let reply = if out.data.is_null() {
                Vec::new()
            } else {
                // SAFETY: the library allocated `len` bytes at `data`.
                unsafe { std::slice::from_raw_parts(out.data, out.len) }.to_vec()
            };
            // SAFETY: releases what the library allocated.
            unsafe { ffi::ea_bytes_free(&mut out) };
            Ok(reply)
        }
        fn select(&mut self, index: u8) -> Result<(), String> {
            // SAFETY: live session.
            check(unsafe { ffi::ea_legacy_select(self.session, index as u64) })
        }
        fn reset(&mut self) -> Result<(), String> {
            // SAFETY: live session.
            check(unsafe { ffi::ea_legacy_reset(self.session) })
        }
        fn abort(&mut self) {
            // SAFETY: live session.
            let _ = unsafe { ffi::ea_legacy_abort(self.session) };
        }
        fn profile_report(&mut self, prefix: &str) {
            if let Ok(p) = text(prefix) {
                // SAFETY: live session, NUL-terminated prefix.
                let _ = unsafe { ffi::ea_profile_report(self.session, p.as_ptr()) };
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn legacy_set_excludes_the_shell_and_the_retired_operations() {
        for code in [8u8, 9, 10, 11, 17, 39, 90, 91, 92] {
            assert!(!is_legacy(code), "{code} is the shell's");
        }
        for code in (18u8..=29).chain([31, 34, 35]) {
            assert!(!is_legacy(code), "{code} is retired");
        }
        for code in [1u8, 7, 12, 16, 30, 32, 33, 36, 38, 40, 45, 53, 60, 66, 80, 81] {
            assert!(is_legacy(code), "{code} is legacy");
        }
        assert!(!is_legacy(0) && !is_legacy(67) && !is_legacy(82) && !is_legacy(255));
    }
}
