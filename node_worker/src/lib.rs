//! The trusted worker shell (REORGANIZATION_PLAN.md stage S8): the C++ shell of
//! `tls_worker_v3.cpp` moved to Rust, once. All sequencing of secret work stays in C++ for
//! now, behind `ea_legacy_dispatch` (engine_abi.h, legacy_abi.cpp).
//!
//! What this crate does, by module:
//! - [`pipe`]: the controller's pipe RPC, unchanged (TlsWorkerPipe.lean:37-38): framing,
//!   sequence numbers, the failure latch.
//! - [`agree`]: both workers agree on every request before acting on it, with today's
//!   private-prefix rule for operations 36, 39, 47 and 53.
//! - [`link`]: THE control link to the other worker (PORT+20) and its frame set [`link::PeerFrame`].
//! - [`server`]: THE server socket, and [`server::ServerOp`], what the shell can do with it.
//! - [`socks`]: the SOCKS5 request built from an agreed connect (no socket of its own).
//! - [`connections`]: the connection table (operation 90), holding [`server::Server`] values.
//! - [`loader`]: strict-mode circuit loading (the manifest, its pins, its agreement).
//! - [`config`]: arguments and environment, and the session string every agreement carries.
//! - [`profile`]: the per-operation measurement lines.
//! - [`engines`]: the engines behind the C ABI (and a trait, so the shell is testable without them).
//! - [`shell`]: one operation: agreement, then the shell's own operations or the legacy library.
//!
//! Only `link.rs` and `server.rs` touch sockets (`tests/socket_owners.rs` checks it).
//!
//! # Design note: what S8 could not do without changing `tls_worker_v3.cpp`
//!
//! The owner's constraint for this step: the `tls-worker-fixture-v3` / `-sh` binaries must
//! keep their behaviour and build outputs, so `tls_worker_v3.cpp` was not edited.
//! `legacy_abi.cpp` therefore includes that file unchanged and calls its `Worker::call`, which
//! has two consequences until the controller switches to this worker (S7) and the C++ shell
//! binaries are retired:
//!
//! 1. **Double agreement.** `Worker::dispatch` agrees on each request itself, on the Boolean
//!    engine's channel, after this shell has agreed it on the control link. One extra message
//!    delay per forwarded operation; same frame, same hash. To remove: when the
//!    `tls-worker*-fixture-v3` binaries are retired, move `Worker::dispatch`'s `switch` into
//!    `legacy_abi.cpp` (the move the plan makes anyway: "dispatch → legacy_dispatch") without
//!    the agreement prologue, and delete `tls_worker_v3.cpp`'s shell parts (pipe loop, SOCKS,
//!    `server_record*`, ops 8-11, 17, 39, 90, 91). The `legacy_operation` list stays.
//! 2. **The unpinned kernel path is unreachable, not absent.** The production library refuses
//!    to open without strict mode (`CIRCUIT_MANIFEST`), so `KernelCache`'s on-demand
//!    production can never run, but its code is compiled in. To remove it from the binary:
//!    guard `kernel.h` lines 124-149 and 175-185 with `#ifdef EMP_HYBRID_ENGINE_ABI_TEST`
//!    (a preprocessor-only change: the existing fixture builds would then also lose it, so do
//!    it together with item 1).
//!
//! Also deferred: the `ServerOp::Close` pipe code (92) is served here but no controller sends
//! it yet (X2).
pub mod agree;
pub mod config;
pub mod connections;
pub mod engines;
pub mod link;
pub mod loader;
pub mod pipe;
pub mod profile;
pub mod server;
pub mod shell;
pub mod socks;
