//! The per-item key chain (Format.lean): c_{i+1} = H("x1-chain-v1" || c_i); the key of item i is
//! H("x1-item-key-v1" || c_i). A `Chain` holds exactly one value, the one at its index; moving
//! forward overwrites it and zeroizes the old one, so the keys of items below the index cannot be
//! computed from what is left (one-wayness of SHA-256). There is no way to move back.

use zeroize::{Zeroize, Zeroizing};

use crate::format::{chain_next, item_key};

/// The index asked for is below the chain's index: its key was erased.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Erased;

pub struct Chain {
    value: Zeroizing<[u8; 32]>,
    index: u64,
}

impl Chain {
    /// A chain at index 0 from a seed (the seed is moved in and the caller's copy zeroized).
    pub fn from_seed(seed: &mut [u8; 32]) -> Chain {
        let chain = Chain { value: Zeroizing::new(*seed), index: 0 };
        seed.zeroize();
        chain
    }

    pub fn index(&self) -> u64 {
        self.index
    }

    fn step(&mut self) {
        let mut next = chain_next(&self.value);
        self.value.zeroize();
        self.value.copy_from_slice(&next);
        next.zeroize();
        self.index += 1;
    }

    /// Move forward to `target` (no-op if already there; never back).
    pub fn advance_to(&mut self, target: u64) {
        while self.index < target {
            self.step();
        }
    }

    /// The key of item `i`, then move past it: afterwards the chain is at `i + 1` and the key of
    /// `i` cannot be derived from it.
    pub fn take_key(&mut self, i: u64) -> Result<Zeroizing<[u8; 32]>, Erased> {
        if i < self.index {
            return Err(Erased);
        }
        self.advance_to(i);
        let key = Zeroizing::new(item_key(&self.value));
        self.step();
        Ok(key)
    }

    /// A second chain at the same index (the producer starts where the user starts).
    pub(crate) fn duplicate(&self) -> Chain {
        Chain { value: Zeroizing::new(*self.value), index: self.index }
    }

    #[cfg(test)]
    pub(crate) fn current_value(&self) -> [u8; 32] {
        *self.value
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn reference(seed: [u8; 32], i: u64) -> [u8; 32] {
        let mut c = seed;
        for _ in 0..i {
            c = chain_next(&c);
        }
        c
    }

    #[test]
    fn keys_follow_the_reference() {
        let seed = [5u8; 32];
        let mut s = seed;
        let mut ch = Chain::from_seed(&mut s);
        assert_eq!(s, [0u8; 32], "seed copy zeroized");
        for i in [0u64, 1, 2, 5, 6, 40] {
            let k = ch.take_key(i).unwrap();
            assert_eq!(*k, item_key(&reference(seed, i)));
            assert_eq!(ch.index(), i + 1);
        }
    }

    /// Old keys are unrecoverable from the current state: after taking item i the chain holds only
    /// c_{i+1}; it holds neither c_j nor the key of j for any j <= i, refuses to give them, and
    /// everything it can still derive is a key of an index above i.
    #[test]
    fn old_keys_unrecoverable() {
        let seed = [9u8; 32];
        let mut s = seed;
        let mut ch = Chain::from_seed(&mut s);
        let mut old = Vec::new();
        for i in 0..20u64 {
            old.push((reference(seed, i), *ch.take_key(i).unwrap()));
        }
        let now = ch.current_value();
        assert_eq!(now, reference(seed, 20));
        for (j, (c, k)) in old.iter().enumerate() {
            assert_ne!(&now, c, "chain value {j} still present");
            assert_ne!(&now, k, "key {j} still present");
            assert_eq!(ch.take_key(j as u64), Err(Erased));
        }
        // what the current value can derive: keys 20, 21, ... none equal to an old key
        let mut probe = ch.duplicate();
        for i in 20..60u64 {
            let k = probe.take_key(i).unwrap();
            assert!(old.iter().all(|(_, ok)| ok != &*k));
        }
    }

    #[test]
    fn never_back() {
        let mut s = [1u8; 32];
        let mut ch = Chain::from_seed(&mut s);
        ch.advance_to(10);
        ch.advance_to(3);
        assert_eq!(ch.index(), 10);
        assert_eq!(ch.take_key(9), Err(Erased));
        assert!(ch.take_key(10).is_ok());
    }
}
