//! The stock's bytes, exactly as `TlsMpc/Node/Stock/Format.lean` defines them (numbers u64
//! little-endian; byte strings a u64 length then the bytes; 32-byte fields raw).

use sha2::{Digest, Sha256};

pub const MAGIC: &[u8; 8] = b"x1-stock";
pub const VERSION: u64 = 1;
/// Tag length of the item cipher.
pub const TAG_LEN: usize = 16;
/// Bytes in front of the sealed bytes of an item record: index, length, agreed hash.
pub const ITEM_HEAD_LEN: usize = 8 + 8 + 32;

pub fn sha256(parts: &[&[u8]]) -> [u8; 32] {
    let mut h = Sha256::new();
    for p in parts {
        h.update(p);
    }
    h.finalize().into()
}

fn put_u64(out: &mut Vec<u8>, n: u64) {
    out.extend_from_slice(&n.to_le_bytes());
}

fn put_bytes(out: &mut Vec<u8>, b: &[u8]) {
    put_u64(out, b.len() as u64);
    out.extend_from_slice(b);
}

/// A reader over a byte slice (the `Dec` monad of Engine.lean).
struct Reader<'a> {
    s: &'a [u8],
}

impl<'a> Reader<'a> {
    fn take(&mut self, n: usize) -> Option<&'a [u8]> {
        if n > self.s.len() {
            return None;
        }
        let (a, b) = self.s.split_at(n);
        self.s = b;
        Some(a)
    }
    fn u64(&mut self) -> Option<u64> {
        Some(u64::from_le_bytes(self.take(8)?.try_into().ok()?))
    }
    fn bytes(&mut self) -> Option<&'a [u8]> {
        let n = self.u64()?;
        self.take(usize::try_from(n).ok()?)
    }
    fn arr32(&mut self) -> Option<[u8; 32]> {
        self.take(32)?.try_into().ok()
    }
}

/// A circuit shape: which lowered circuit, which size class, which client profile.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ShapeId {
    pub circuit: Vec<u8>,
    pub size_class: u64,
    pub profile: Vec<u8>,
}

impl ShapeId {
    pub fn new(circuit: &str, size_class: u64, profile: &str) -> ShapeId {
        ShapeId { circuit: circuit.as_bytes().to_vec(), size_class, profile: profile.as_bytes().to_vec() }
    }

    /// `ShapeId.enc`.
    pub fn enc(&self) -> Vec<u8> {
        let mut out = Vec::new();
        put_bytes(&mut out, &self.circuit);
        put_u64(&mut out, self.size_class);
        put_bytes(&mut out, &self.profile);
        out
    }

    /// The key of the shape in boot memory and its directory name.
    pub fn key(&self) -> [u8; 32] {
        sha256(&[b"x1-shape-v1", &self.enc()])
    }

    pub fn dir_name(&self) -> String {
        hex(&self.key()[..16])
    }

    fn dec(r: &mut Reader) -> Option<ShapeId> {
        let circuit = r.bytes()?.to_vec();
        let size_class = r.u64()?;
        let profile = r.bytes()?.to_vec();
        Some(ShapeId { circuit, size_class, profile })
    }
}

/// A stock's header (`Format.Header`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Header {
    pub shape: ShapeId,
    pub manifest: [u8; 32],
    pub boot_id: [u8; 32],
    pub stock_id: [u8; 32],
    pub item_len: u64,
}

impl Header {
    /// `encHeader`.
    pub fn enc(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(MAGIC);
        put_u64(&mut out, VERSION);
        out.extend_from_slice(&self.shape.enc());
        out.extend_from_slice(&self.manifest);
        out.extend_from_slice(&self.boot_id);
        out.extend_from_slice(&self.stock_id);
        put_u64(&mut out, self.item_len);
        out
    }

    /// `parseHeader`: the whole input must be one header.
    pub fn parse(s: &[u8]) -> Option<Header> {
        let mut r = Reader { s };
        if r.take(8)? != MAGIC || r.u64()? != VERSION {
            return None;
        }
        let shape = ShapeId::dec(&mut r)?;
        let manifest = r.arr32()?;
        let boot_id = r.arr32()?;
        let stock_id = r.arr32()?;
        let item_len = r.u64()?;
        if !r.s.is_empty() {
            return None;
        }
        Some(Header { shape, manifest, boot_id, stock_id, item_len })
    }

    /// `recordLen itemLen`.
    pub fn record_len(&self) -> u64 {
        record_len(self.item_len)
    }
}

pub fn record_len(item_len: u64) -> u64 {
    ITEM_HEAD_LEN as u64 + item_len + TAG_LEN as u64
}

/// What is stored in the clear in front of an item's sealed bytes (`Format.ItemHead`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ItemHead {
    pub index: u64,
    pub length: u64,
    pub agreed: [u8; 32],
}

impl ItemHead {
    /// `encItem`.
    pub fn enc_item(&self, sealed: &[u8]) -> Vec<u8> {
        let mut out = Vec::with_capacity(ITEM_HEAD_LEN + sealed.len());
        put_u64(&mut out, self.index);
        put_u64(&mut out, self.length);
        out.extend_from_slice(&self.agreed);
        out.extend_from_slice(sealed);
        out
    }

    /// `decItem` over a whole record: the head and the sealed bytes.
    pub fn dec_item(s: &[u8]) -> Option<(ItemHead, Vec<u8>)> {
        let mut r = Reader { s };
        let index = r.u64()?;
        let length = r.u64()?;
        let agreed = r.arr32()?;
        let sealed = r.take(usize::try_from(length).ok()?.checked_add(TAG_LEN)?)?.to_vec();
        if !r.s.is_empty() {
            return None;
        }
        Some((ItemHead { index, length, agreed }, sealed))
    }

    /// Only the head (for reading the agreed hash before the item is taken).
    pub fn dec_head(s: &[u8]) -> Option<ItemHead> {
        let mut r = Reader { s };
        Some(ItemHead { index: r.u64()?, length: r.u64()?, agreed: r.arr32()? })
    }
}

/// `itemAad`: the associated data binding an item to its boot, stock, circuits, shape and index.
pub fn item_aad(h: &Header, it: &ItemHead) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(b"x1-item-v1");
    out.extend_from_slice(&h.boot_id);
    out.extend_from_slice(&h.stock_id);
    out.extend_from_slice(&h.manifest);
    out.extend_from_slice(&h.shape.enc());
    put_u64(&mut out, it.index);
    put_u64(&mut out, it.length);
    out.extend_from_slice(&it.agreed);
    out
}

/// `journalTag sha256 stockId w`.
pub fn journal_tag(stock_id: &[u8; 32], w: u64) -> [u8; 8] {
    let h = sha256(&[b"x1-journal-v1", stock_id, &w.to_le_bytes()]);
    h[..8].try_into().expect("8 bytes")
}

/// `chainNext sha256`.
pub fn chain_next(c: &[u8; 32]) -> [u8; 32] {
    sha256(&[b"x1-chain-v1", c])
}

/// `itemKey sha256`.
pub fn item_key(c: &[u8; 32]) -> [u8; 32] {
    sha256(&[b"x1-item-key-v1", c])
}

/// `encClaim`: a node's next index in the per-message agreement, or none.
pub fn enc_claim(c: Option<u64>) -> Vec<u8> {
    match c {
        None => vec![0],
        Some(n) => {
            let mut out = vec![1];
            put_u64(&mut out, n);
            out
        }
    }
}

/// `decClaim`.
pub fn dec_claim(s: &[u8]) -> Option<Option<u64>> {
    match s {
        [0] => Some(None),
        [1, rest @ ..] if rest.len() == 8 => Some(Some(u64::from_le_bytes(rest.try_into().ok()?))),
        _ => None,
    }
}

/// Provisional opcode of the specified `stockUse` instruction (Use.lean, SPECIFICATION).
pub const OP_STOCK_USE: u8 = 22;

/// `encStockUse`.
pub fn enc_stock_use(shape: &ShapeId, index: u64, agreed: &[u8; 32]) -> Vec<u8> {
    let mut out = vec![OP_STOCK_USE];
    out.extend_from_slice(&shape.enc());
    put_u64(&mut out, index);
    out.extend_from_slice(agreed);
    out
}

pub fn hex(b: &[u8]) -> String {
    const D: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(b.len() * 2);
    for &x in b {
        s.push(D[(x >> 4) as usize] as char);
        s.push(D[(x & 15) as usize] as char);
    }
    s
}

pub fn unhex(s: &str) -> Option<Vec<u8>> {
    if s.len() % 2 != 0 {
        return None;
    }
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).ok()).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn header() -> Header {
        Header {
            shape: ShapeId::new("signal-seal-official", 3, "official"),
            manifest: [1; 32],
            boot_id: [2; 32],
            stock_id: [3; 32],
            item_len: 1000,
        }
    }

    #[test]
    fn header_round_trip() {
        let h = header();
        assert_eq!(Header::parse(&h.enc()), Some(h.clone()));
        let mut long = h.enc();
        long.push(0);
        assert_eq!(Header::parse(&long), None);
        for n in 0..h.enc().len() {
            assert_eq!(Header::parse(&h.enc()[..n]), None, "prefix {n}");
        }
        let mut bad = h.enc();
        bad[0] ^= 1;
        assert_eq!(Header::parse(&bad), None);
    }

    #[test]
    fn item_round_trip() {
        let it = ItemHead { index: 7, length: 5, agreed: [9; 32] };
        let sealed = vec![4u8; 5 + TAG_LEN];
        let rec = it.enc_item(&sealed);
        assert_eq!(rec.len() as u64, record_len(5));
        assert_eq!(ItemHead::dec_item(&rec), Some((it.clone(), sealed)));
        assert_eq!(ItemHead::dec_head(&rec), Some(it));
        assert_eq!(ItemHead::dec_item(&rec[..rec.len() - 1]), None);
    }

    #[test]
    fn claims() {
        for c in [None, Some(0), Some(5), Some(u64::MAX)] {
            assert_eq!(dec_claim(&enc_claim(c)), Some(c));
        }
        assert_eq!(dec_claim(&[1, 0]), None);
        assert_eq!(dec_claim(&[2]), None);
    }
}
