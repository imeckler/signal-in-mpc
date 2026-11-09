// PUBLIC-FIXTURE-only forwarding entries; the preceding vendor source is unchanged.
pub fn fixture_add_key(state: &mut [u64; 8], keys: &[u64]) { add_round_key(state, keys); }
pub fn fixture_inverse(words: &[u64]) -> Vec<Vec<u8>> {
    inv_bitslice(words).iter().map(|block| block.to_vec()).collect()
}
