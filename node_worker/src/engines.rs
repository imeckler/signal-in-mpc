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

    // ---- S9: the instruction set's engine calls (interp.rs), one per engine_abi.h function.
    // Handles are the engines' own. Bits are one byte each (0/1), elements 32 bytes
    // little-endian. The defaults refuse: an `Engines` without them runs no batch.

    /// `ea_circuit_load` then `ea_circuit_shape`: (circuit, input bits, output bits).
    fn circuit_load(&mut self, _path: &str, _sha256: &str) -> Result<(u64, u32, u32), String> {
        no_instructions()
    }
    /// `ea_bool_input_private` (`owner` 0 or 1; the non-owner passes placeholder bits).
    fn bool_input_private(&mut self, _owner: u8, _bits: &[u8]) -> Result<u64, String> {
        no_instructions()
    }
    /// `ea_bool_input_both`: (party 0's handle, party 1's handle).
    fn bool_input_both(&mut self, _bits: &[u8]) -> Result<(u64, u64), String> {
        no_instructions()
    }
    fn bool_public(&mut self, _bits: &[u8]) -> Result<u64, String> {
        no_instructions()
    }
    fn bool_run(&mut self, _circuit: u64, _copies: u32, _input: u64) -> Result<u64, String> {
        no_instructions()
    }
    /// `ea_bool_open`: `count` (the handle's width) opened bits.
    fn bool_open(&mut self, _h: u64, _count: usize) -> Result<Vec<u8>, String> {
        no_instructions()
    }
    /// `ea_bool_open_to`: the recipient's bits; the other party's are all zero.
    fn bool_open_to(&mut self, _h: u64, _recipient: u8, _count: usize) -> Result<Vec<u8>, String> {
        no_instructions()
    }
    fn bool_concat(&mut self, _hs: &[u64]) -> Result<u64, String> {
        no_instructions()
    }
    fn bool_pick(&mut self, _h: u64, _indices: &[u64]) -> Result<u64, String> {
        no_instructions()
    }
    fn bool_slice(&mut self, _h: u64, _lo: usize, _hi: usize) -> Result<u64, String> {
        no_instructions()
    }
    fn bool_free(&mut self, _h: u64) -> Result<(), String> {
        no_instructions()
    }
    /// `ea_field_input_coins`: (party 0's handles, party 1's handles).
    fn field_input_coins(&mut self, _local: &[u64]) -> Result<(Vec<u64>, Vec<u64>), String> {
        no_instructions()
    }
    /// `ea_field_input_elements`: (party 0's handles, party 1's handles).
    fn field_input_elements(&mut self, _local: &[[u8; 32]]) -> Result<(Vec<u64>, Vec<u64>), String> {
        no_instructions()
    }
    fn field_constant(&mut self, _value: u64) -> Result<u64, String> {
        no_instructions()
    }
    fn field_public(&mut self, _value: &[u8; 32]) -> Result<u64, String> {
        no_instructions()
    }
    fn field_add(&mut self, _a: u64, _b: u64) -> Result<u64, String> {
        no_instructions()
    }
    fn field_sub(&mut self, _a: u64, _b: u64) -> Result<u64, String> {
        no_instructions()
    }
    fn field_scale(&mut self, _a: u64, _constant: u64) -> Result<u64, String> {
        no_instructions()
    }
    fn field_divide_public(&mut self, _a: u64, _c: &[u8; 32]) -> Result<u64, String> {
        no_instructions()
    }
    fn field_mul(&mut self, _a: &[u64], _b: &[u64]) -> Result<Vec<u64>, String> {
        no_instructions()
    }
    fn field_check(&mut self) -> Result<(), String> {
        no_instructions()
    }
    /// `ea_field_checked_open`: the opened elements.
    fn field_checked_open(&mut self, _hs: &[u64]) -> Result<Vec<[u8; 32]>, String> {
        no_instructions()
    }
    fn field_free(&mut self, _h: u64) -> Result<(), String> {
        no_instructions()
    }
}

fn no_instructions<T>() -> Result<T, String> {
    Err("these engines run no instructions".into())
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

    /// engine_abi.h: the session and legacy part (S8) and the Boolean and field instruction
    /// functions (S9, used by interp.rs through [`Engines`]). `ea_bool_interleave` and
    /// `ea_bool_width` are not used (Engine.lean design note, item 3).
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
            pub fn ea_circuit_load(session: *mut ea_session, path: *const c_char, sha256_hex: *const c_char, out: *mut u64) -> c_int;
            pub fn ea_circuit_shape(session: *mut ea_session, circuit: u64, input_bits: *mut u32, output_bits: *mut u32) -> c_int;
            pub fn ea_bool_input_private(session: *mut ea_session, owner: c_int, bits: *const u8, count: usize, out: *mut u64) -> c_int;
            pub fn ea_bool_input_both(session: *mut ea_session, bits: *const u8, count: usize, out_a: *mut u64, out_b: *mut u64) -> c_int;
            pub fn ea_bool_public(session: *mut ea_session, bits: *const u8, count: usize, out: *mut u64) -> c_int;
            pub fn ea_bool_run(session: *mut ea_session, circuit: u64, copies: u32, input: u64, out: *mut u64) -> c_int;
            pub fn ea_bool_open(session: *mut ea_session, handle: u64, bits: *mut u8, count: usize) -> c_int;
            pub fn ea_bool_open_to(session: *mut ea_session, handle: u64, recipient: c_int, bits: *mut u8, count: usize) -> c_int;
            pub fn ea_bool_concat(session: *mut ea_session, handles: *const u64, count: usize, out: *mut u64) -> c_int;
            pub fn ea_bool_pick(session: *mut ea_session, handle: u64, indices: *const u64, count: usize, out: *mut u64) -> c_int;
            pub fn ea_bool_slice(session: *mut ea_session, handle: u64, lo: usize, hi: usize, out: *mut u64) -> c_int;
            pub fn ea_bool_free(session: *mut ea_session, handle: u64) -> c_int;
            pub fn ea_field_input_coins(session: *mut ea_session, local: *const u64, count: usize, outs_a: *mut u64, outs_b: *mut u64) -> c_int;
            pub fn ea_field_input_elements(session: *mut ea_session, local: *const u8, count: usize, outs_a: *mut u64, outs_b: *mut u64) -> c_int;
            pub fn ea_field_constant(session: *mut ea_session, value: u64, out: *mut u64) -> c_int;
            pub fn ea_field_public(session: *mut ea_session, element: *const u8, out: *mut u64) -> c_int;
            pub fn ea_field_add(session: *mut ea_session, a: u64, b: u64, out: *mut u64) -> c_int;
            pub fn ea_field_sub(session: *mut ea_session, a: u64, b: u64, out: *mut u64) -> c_int;
            pub fn ea_field_scale(session: *mut ea_session, a: u64, constant: u64, out: *mut u64) -> c_int;
            pub fn ea_field_divide_public(session: *mut ea_session, a: u64, c: *const u8, out: *mut u64) -> c_int;
            pub fn ea_field_mul(session: *mut ea_session, a: *const u64, b: *const u64, count: usize, outs: *mut u64) -> c_int;
            pub fn ea_field_check(session: *mut ea_session) -> c_int;
            pub fn ea_field_checked_open(session: *mut ea_session, handles: *const u64, count: usize, out: *mut u8) -> c_int;
            pub fn ea_field_free(session: *mut ea_session, handle: u64) -> c_int;
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

        // SAFETY (every call below): the session is live; every input pointer comes from a
        // slice or array valid for the stated count; every output pointer refers to a local or
        // to a buffer of exactly the count the ABI writes.
        fn circuit_load(&mut self, path: &str, sha256: &str) -> Result<(u64, u32, u32), String> {
            let (p, s) = (text(path)?, text(sha256)?);
            let mut c = 0u64;
            check(unsafe { ffi::ea_circuit_load(self.session, p.as_ptr(), s.as_ptr(), &mut c) })?;
            let (mut i, mut o) = (0u32, 0u32);
            check(unsafe { ffi::ea_circuit_shape(self.session, c, &mut i, &mut o) })?;
            Ok((c, i, o))
        }
        fn bool_input_private(&mut self, owner: u8, bits: &[u8]) -> Result<u64, String> {
            let mut h = 0u64;
            check(unsafe { ffi::ea_bool_input_private(self.session, owner as c_int, bits.as_ptr(), bits.len(), &mut h) })?;
            Ok(h)
        }
        fn bool_input_both(&mut self, bits: &[u8]) -> Result<(u64, u64), String> {
            let (mut a, mut b) = (0u64, 0u64);
            check(unsafe { ffi::ea_bool_input_both(self.session, bits.as_ptr(), bits.len(), &mut a, &mut b) })?;
            Ok((a, b))
        }
        fn bool_public(&mut self, bits: &[u8]) -> Result<u64, String> {
            let mut h = 0u64;
            check(unsafe { ffi::ea_bool_public(self.session, bits.as_ptr(), bits.len(), &mut h) })?;
            Ok(h)
        }
        fn bool_run(&mut self, circuit: u64, copies: u32, input: u64) -> Result<u64, String> {
            let mut h = 0u64;
            check(unsafe { ffi::ea_bool_run(self.session, circuit, copies, input, &mut h) })?;
            Ok(h)
        }
        fn bool_open(&mut self, h: u64, count: usize) -> Result<Vec<u8>, String> {
            let mut bits = vec![0u8; count];
            check(unsafe { ffi::ea_bool_open(self.session, h, bits.as_mut_ptr(), count) })?;
            Ok(bits)
        }
        fn bool_open_to(&mut self, h: u64, recipient: u8, count: usize) -> Result<Vec<u8>, String> {
            let mut bits = vec![0u8; count];
            check(unsafe { ffi::ea_bool_open_to(self.session, h, recipient as c_int, bits.as_mut_ptr(), count) })?;
            Ok(bits)
        }
        fn bool_concat(&mut self, hs: &[u64]) -> Result<u64, String> {
            let mut h = 0u64;
            check(unsafe { ffi::ea_bool_concat(self.session, hs.as_ptr(), hs.len(), &mut h) })?;
            Ok(h)
        }
        fn bool_pick(&mut self, h: u64, indices: &[u64]) -> Result<u64, String> {
            let mut out = 0u64;
            check(unsafe { ffi::ea_bool_pick(self.session, h, indices.as_ptr(), indices.len(), &mut out) })?;
            Ok(out)
        }
        fn bool_slice(&mut self, h: u64, lo: usize, hi: usize) -> Result<u64, String> {
            let mut out = 0u64;
            check(unsafe { ffi::ea_bool_slice(self.session, h, lo, hi, &mut out) })?;
            Ok(out)
        }
        fn bool_free(&mut self, h: u64) -> Result<(), String> {
            check(unsafe { ffi::ea_bool_free(self.session, h) })
        }
        fn field_input_coins(&mut self, local: &[u64]) -> Result<(Vec<u64>, Vec<u64>), String> {
            let (mut a, mut b) = (vec![0u64; local.len()], vec![0u64; local.len()]);
            check(unsafe { ffi::ea_field_input_coins(self.session, local.as_ptr(), local.len(), a.as_mut_ptr(), b.as_mut_ptr()) })?;
            Ok((a, b))
        }
        fn field_input_elements(&mut self, local: &[[u8; 32]]) -> Result<(Vec<u64>, Vec<u64>), String> {
            let flat: Vec<u8> = local.concat();
            let (mut a, mut b) = (vec![0u64; local.len()], vec![0u64; local.len()]);
            check(unsafe { ffi::ea_field_input_elements(self.session, flat.as_ptr(), local.len(), a.as_mut_ptr(), b.as_mut_ptr()) })?;
            Ok((a, b))
        }
        fn field_constant(&mut self, value: u64) -> Result<u64, String> {
            let mut h = 0u64;
            check(unsafe { ffi::ea_field_constant(self.session, value, &mut h) })?;
            Ok(h)
        }
        fn field_public(&mut self, value: &[u8; 32]) -> Result<u64, String> {
            let mut h = 0u64;
            check(unsafe { ffi::ea_field_public(self.session, value.as_ptr(), &mut h) })?;
            Ok(h)
        }
        fn field_add(&mut self, a: u64, b: u64) -> Result<u64, String> {
            let mut h = 0u64;
            check(unsafe { ffi::ea_field_add(self.session, a, b, &mut h) })?;
            Ok(h)
        }
        fn field_sub(&mut self, a: u64, b: u64) -> Result<u64, String> {
            let mut h = 0u64;
            check(unsafe { ffi::ea_field_sub(self.session, a, b, &mut h) })?;
            Ok(h)
        }
        fn field_scale(&mut self, a: u64, constant: u64) -> Result<u64, String> {
            let mut h = 0u64;
            check(unsafe { ffi::ea_field_scale(self.session, a, constant, &mut h) })?;
            Ok(h)
        }
        fn field_divide_public(&mut self, a: u64, c: &[u8; 32]) -> Result<u64, String> {
            let mut h = 0u64;
            check(unsafe { ffi::ea_field_divide_public(self.session, a, c.as_ptr(), &mut h) })?;
            Ok(h)
        }
        fn field_mul(&mut self, a: &[u64], b: &[u64]) -> Result<Vec<u64>, String> {
            if a.len() != b.len() {
                return Err("mul arguments".into());
            }
            let mut outs = vec![0u64; a.len()];
            check(unsafe { ffi::ea_field_mul(self.session, a.as_ptr(), b.as_ptr(), a.len(), outs.as_mut_ptr()) })?;
            Ok(outs)
        }
        fn field_check(&mut self) -> Result<(), String> {
            check(unsafe { ffi::ea_field_check(self.session) })
        }
        fn field_checked_open(&mut self, hs: &[u64]) -> Result<Vec<[u8; 32]>, String> {
            let mut out = vec![0u8; 32 * hs.len()];
            check(unsafe { ffi::ea_field_checked_open(self.session, hs.as_ptr(), hs.len(), out.as_mut_ptr()) })?;
            Ok(out.chunks_exact(32).map(|c| c.try_into().unwrap()).collect())
        }
        fn field_free(&mut self, h: u64) -> Result<(), String> {
            check(unsafe { ffi::ea_field_free(self.session, h) })
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
