//! Boot memory: the boot id and, per shape, the stock's key state. Held only in memory, never
//! written anywhere (the boot id is copied into the headers of stocks made during this boot).
//!
//! In the Lean model (Use.lean) this is the `boot` and `key` of a node: it survives a crash of the
//! process that uses the stock and is lost at a reboot. Here it is an ordinary value shared with
//! the store through `Arc<Mutex<_>>`; a `Store` can be dropped (a crash) and opened again with the
//! same `BootMemory`. To survive a crash of the worker process in deployment it must live in a
//! longer-lived holder (a small key-holder process, or a kernel keyring); that holder is not built
//! (STOCK.md). If it lives in the worker itself, a worker crash loses it, and every stock becomes
//! unusable, which is safe.

use std::collections::HashMap;
use std::io;

use zeroize::Zeroize;

use crate::chain::Chain;
use crate::random::random32;

/// The key state of one shape's stock (Lean `Key`): the stock id, the use cursor and the use
/// chain, the producer cursor and the producer chain (at the next index to write).
///
/// The use chain's own index never exceeds the use cursor: every index below the use cursor that
/// has an item on disk has had its chain value erased. Indices skipped beyond the last item on disk
/// (a peer far ahead) move the cursor without hashing that far: no item exists there, so there
/// is no key to erase, and a lying peer cannot make the node hash 2^64 times.
pub struct StockKey {
    pub(crate) stock_id: [u8; 32],
    pub(crate) use_index: u64,
    pub(crate) use_chain: Chain,
    pub(crate) prod_index: u64,
    pub(crate) prod_chain: Chain,
}

impl StockKey {
    pub(crate) fn new(stock_id: [u8; 32], mut seed: [u8; 32]) -> StockKey {
        let prod_chain = Chain::from_seed(&mut seed);
        let use_chain = prod_chain.duplicate();
        StockKey { stock_id, use_index: 0, use_chain, prod_index: 0, prod_chain }
    }

    /// Move the use cursor forward to `target` (never back), erasing the chain values of the
    /// items on disk (`count` of them) that it passes.
    pub(crate) fn advance_use(&mut self, target: u64, count: u64) {
        if target <= self.use_index {
            return;
        }
        self.use_chain.advance_to(target.min(count));
        self.use_index = target;
    }

    #[cfg(test)]
    pub(crate) fn duplicate(&self) -> StockKey {
        StockKey {
            stock_id: self.stock_id,
            use_index: self.use_index,
            use_chain: self.use_chain.duplicate(),
            prod_index: self.prod_index,
            prod_chain: self.prod_chain.duplicate(),
        }
    }
}

pub struct BootMemory {
    boot_id: [u8; 32],
    pub(crate) shapes: HashMap<[u8; 32], StockKey>,
}

impl BootMemory {
    /// A new boot: a fresh random boot id, no stock keys.
    pub fn new() -> io::Result<BootMemory> {
        Ok(BootMemory { boot_id: random32()?, shapes: HashMap::new() })
    }

    pub fn boot_id(&self) -> [u8; 32] {
        self.boot_id
    }

    /// Forget a shape's stock key (the stock becomes unusable).
    pub fn forget(&mut self, shape_key: &[u8; 32]) {
        self.shapes.remove(shape_key);
    }
}

impl Drop for BootMemory {
    fn drop(&mut self) {
        self.boot_id.zeroize();
    }
}
