//! X1: the encrypted on-disk STOCK of message-independent preprocessing (garbled circuits,
//! authenticated triples) made ahead in quiet hours and used exactly once.
//!
//! Design: `STOCK.md` at the repository root. Model and proofs: `TlsMpc/Node/Stock/` (Journal.lean:
//! the journal and its crash semantics; Format.lean: the bytes; Use.lean: the use rule and T14).
//! This crate implements the store side of the model: the per-shape files, the consumed journal
//! (append + fsync before use, torn tails dropped), the in-memory boot id and key chain (advanced
//! and the old value erased on use), and authenticated encryption per item bound to (boot id,
//! stock id, manifest, shape, index). It is standalone: nothing calls it yet (the engine's
//! `export_preprocessing` / `import_preprocessing` and the `stockUse` instruction are specified,
//! not built).
//!
//! Correspondence with the Lean model (`Use.lean`):
//!   `Store::take`        = start j; sync; decrypt; hand
//!   `Store::skip_to`     = skip j
//!   `Store::create`      = newStock
//!   `Store::put` (k x)   = extend k
//!   drop the `Store`, `Store::open` again with the same `BootMemory` = crash (then restart)
//!   a new `BootMemory`  = reboot
//!   `Store::next_index`  = NodeState.next production (when usable)
//! The test `vectors` replays schedules generated from the Lean model and checks every outcome.

pub mod agree;
pub mod boot;
pub mod chain;
pub mod cipher;
pub mod format;
pub mod journal;
pub mod random;
pub mod store;

pub use boot::BootMemory;
pub use cipher::{ChaChaCipher, ItemCipher, NullCipher};
pub use format::ShapeId;
pub use store::{Item, StockError, Store};

#[cfg(test)]
mod vectors;
