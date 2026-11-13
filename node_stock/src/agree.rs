//! The pair rule (Use.lean `agreeIndex`): each node sends its next index for the shape (or none),
//! and both use the larger. Never back; no stock on either side means live preprocessing.

pub fn agree_index(mine: Option<u64>, peer: Option<u64>) -> Option<u64> {
    match (mine, peer) {
        (Some(a), Some(b)) => Some(a.max(b)),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rule() {
        assert_eq!(agree_index(Some(3), Some(5)), Some(5));
        assert_eq!(agree_index(Some(5), Some(3)), Some(5));
        assert_eq!(agree_index(Some(3), None), None);
        assert_eq!(agree_index(None, Some(3)), None);
        // never back, whatever the peer claims
        for peer in [0u64, 1, 2, 1 << 40] {
            assert!(agree_index(Some(2), Some(peer)).unwrap() >= 2);
        }
    }
}
