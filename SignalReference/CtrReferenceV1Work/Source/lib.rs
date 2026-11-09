//! Reference entrypoints only: unchanged pinned ctr methods at AES blocksize16.
//! No supplied validity/crypto primitive and no replacement counter algorithm.
use ctr::cipher::{array::Array,typenum::U16};
use ctr::flavors::{Ctr32BE,CtrFlavor};
pub type Block = Array<u8,U16>;
pub type State = <Ctr32BE as CtrFlavor<U16>>::CtrNonce;
pub fn current(state: &State) -> Block {<Ctr32BE as CtrFlavor<U16>>::current_block(state)}
pub fn next(state: &mut State) -> Block {<Ctr32BE as CtrFlavor<U16>>::next_block(state)}
pub fn from_nonce(nonce: &Block) -> State {<Ctr32BE as CtrFlavor<U16>>::from_nonce(nonce)}
pub fn remaining(state: &State) -> Option<usize> {<Ctr32BE as CtrFlavor<U16>>::remaining(state)}
