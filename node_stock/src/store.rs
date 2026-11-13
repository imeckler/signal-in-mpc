//! The encrypted store: one directory per shape, three files (`header`, `items`, `journal`), all
//! keys in boot memory.
//!
//! Using an item (`take`), in this order, as the Lean model's `start; sync; decrypt; hand`:
//!   1. checks: the stock is usable (header made in this boot, boot memory holds its key), the
//!      index is not below the next index (`behind`), the item exists (`absent`);
//!   2. the index is appended to the journal and the journal is synced (fsync);
//!   3. the item's key is derived from the use chain, the chain moves past the index and the old
//!      chain values are zeroized: from now on the item cannot be decrypted by anyone;
//!   4. the item is decrypted and verified (associated data: boot id, stock id, manifest, shape,
//!      index, length, agreed hash) and returned.
//! A crash between any two steps leaves the item unused and consumed (wasted, never reused).
//!
//! Making an item (`put`): items are written in index order; the producer chain gives the item's
//! key and moves past it BEFORE the record is written, so no key ever encrypts two plaintexts,
//! even if a crash interrupts the write (the stock then takes no more items: `exhausted`).

use std::collections::HashMap;
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::os::unix::fs::FileExt;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

use zeroize::Zeroizing;

use crate::boot::{BootMemory, StockKey};
use crate::cipher::ItemCipher;
use crate::format::{Header, ItemHead, ShapeId, item_aad};
use crate::journal::JournalFile;
use crate::random::random32;

#[derive(Debug)]
pub enum StockError {
    /// No stock of this shape made in this boot whose key boot memory holds (or a corrupt one).
    Unusable,
    /// The index is below the next index: it was used or skipped.
    Behind,
    /// No item at this index (not made yet, or beyond the stock).
    Absent,
    /// The item's key is erased (the use cursor is past it).
    Erased,
    /// The stock takes no more items (the use cursor passed the producer, or a write was cut).
    Exhausted,
    /// `put` must write the next index.
    OutOfOrder,
    /// `put` with bytes of the wrong length.
    BadLength,
    /// `take_expect`: the item's agreed hash is not the expected one (nothing consumed).
    WrongHash,
    /// The record does not decode or does not verify (the index is consumed).
    Corrupt,
    Io(io::Error),
    /// Test hook: the operation was cut at a chosen step (a simulated crash).
    #[cfg(test)]
    Cut,
}

impl StockError {
    /// The Lean `Refusal` name, where there is one.
    pub fn name(&self) -> &'static str {
        match self {
            StockError::Unusable => "unusable",
            StockError::Behind => "behind",
            StockError::Absent => "absent",
            StockError::Erased => "erased",
            StockError::Exhausted => "exhausted",
            StockError::OutOfOrder => "out-of-order",
            StockError::BadLength => "bad-length",
            StockError::WrongHash => "wrong-hash",
            StockError::Corrupt => "corrupt",
            StockError::Io(_) => "io",
            #[cfg(test)]
            StockError::Cut => "cut",
        }
    }
}

impl From<io::Error> for StockError {
    fn from(e: io::Error) -> StockError {
        StockError::Io(e)
    }
}

/// An item taken from the stock: its bytes (zeroized when dropped) and its agreed hash.
pub struct Item {
    pub index: u64,
    pub bytes: Zeroizing<Vec<u8>>,
    pub agreed: [u8; 32],
}

/// One shape's files, as read when the store (re)opened them.
struct ShapeFiles {
    header: Option<Header>,
    journal: Option<JournalFile>,
    items: Option<File>,
    count: u64,
}

impl ShapeFiles {
    fn read(dir: &Path, shape: &ShapeId) -> io::Result<ShapeFiles> {
        let none = ShapeFiles { header: None, journal: None, items: None, count: 0 };
        let mut bytes = Vec::new();
        match File::open(dir.join("header")) {
            Ok(mut f) => {
                f.read_to_end(&mut bytes)?;
            }
            Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(none),
            Err(e) => return Err(e),
        }
        let header = match Header::parse(&bytes) {
            Some(h) if &h.shape == shape => h,
            _ => return Ok(none),
        };
        let journal = match JournalFile::open(&dir.join("journal"), header.stock_id) {
            Ok(Ok(j)) => j,
            Ok(Err(_corrupt)) => return Ok(none),
            Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(none),
            Err(e) => return Err(e),
        };
        let items = match OpenOptions::new().read(true).write(true).open(dir.join("items")) {
            Ok(f) => f,
            Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(none),
            Err(e) => return Err(e),
        };
        let count = items.metadata()?.len() / header.record_len();
        Ok(ShapeFiles { header: Some(header), journal: Some(journal), items: Some(items), count })
    }
}

/// The parts of a usable stock, borrowed together.
struct Usable<'a> {
    header: &'a Header,
    journal: &'a mut JournalFile,
    items: &'a File,
    count: &'a mut u64,
    key: &'a mut StockKey,
}

impl Usable<'_> {
    fn next(&self) -> u64 {
        self.journal.next().max(self.key.use_index)
    }
}

fn usable<'a>(files: &'a mut ShapeFiles, boot: &'a mut BootMemory, shape_key: &[u8; 32]) -> Result<Usable<'a>, StockError> {
    let boot_id = boot.boot_id();
    let (Some(header), Some(journal), Some(items)) = (files.header.as_ref(), files.journal.as_mut(), files.items.as_ref()) else {
        return Err(StockError::Unusable);
    };
    let Some(key) = boot.shapes.get_mut(shape_key) else {
        return Err(StockError::Unusable);
    };
    if header.boot_id != boot_id || header.stock_id != key.stock_id {
        return Err(StockError::Unusable);
    }
    Ok(Usable { header, journal, items, count: &mut files.count, key })
}

fn sync_dir(dir: &Path) -> io::Result<()> {
    File::open(dir)?.sync_all()
}

pub struct Store<C: ItemCipher> {
    root: PathBuf,
    boot: Arc<Mutex<BootMemory>>,
    cipher: C,
    shapes: HashMap<[u8; 32], ShapeFiles>,
    /// Test hook: cut the next `take` after step 0 (appended), 1 (synced) or 2 (key erased).
    #[cfg(test)]
    pub(crate) cut_at: Option<u8>,
}

impl<C: ItemCipher> Store<C> {
    /// Open the store under `root` (created if missing). Shapes are read when first used; opening
    /// a journal drops its torn tail.
    pub fn open(root: &Path, boot: Arc<Mutex<BootMemory>>, cipher: C) -> io::Result<Store<C>> {
        fs::create_dir_all(root)?;
        Ok(Store {
            root: root.to_path_buf(),
            boot,
            cipher,
            shapes: HashMap::new(),
            #[cfg(test)]
            cut_at: None,
        })
    }

    fn dir(&self, shape: &ShapeId) -> PathBuf {
        self.root.join(shape.dir_name())
    }

    fn ensure(&mut self, shape: &ShapeId) -> io::Result<[u8; 32]> {
        let key = shape.key();
        if !self.shapes.contains_key(&key) {
            let files = ShapeFiles::read(&self.dir(shape), shape)?;
            self.shapes.insert(key, files);
        }
        Ok(key)
    }

    /// Make a new, empty stock of `shape` (replacing any stock of that shape): a fresh stock id,
    /// a fresh chain seed in boot memory, the header carrying this boot's id.
    pub fn create(&mut self, shape: &ShapeId, item_len: u64, manifest: [u8; 32]) -> Result<[u8; 32], StockError> {
        let boot_arc = Arc::clone(&self.boot);
        let mut boot = boot_arc.lock().expect("boot memory");
        let key = shape.key();
        boot.forget(&key);
        self.shapes.remove(&key);
        let dir = self.dir(shape);
        fs::create_dir_all(&dir)?;
        for name in ["header", "journal", "items", "header.new"] {
            match fs::remove_file(dir.join(name)) {
                Err(e) if e.kind() != io::ErrorKind::NotFound => return Err(e.into()),
                _ => {}
            }
        }
        sync_dir(&dir)?;
        let stock_id = random32()?;
        let seed = random32()?;
        let header = Header { shape: shape.clone(), manifest, boot_id: boot.boot_id(), stock_id, item_len };
        let journal = JournalFile::create(&dir.join("journal"), stock_id)?;
        let items = OpenOptions::new().read(true).write(true).create(true).truncate(true).open(dir.join("items"))?;
        items.sync_all()?;
        {
            let mut f = File::create(dir.join("header.new"))?;
            f.write_all(&header.enc())?;
            f.sync_all()?;
        }
        fs::rename(dir.join("header.new"), dir.join("header"))?;
        sync_dir(&dir)?;
        boot.shapes.insert(key, StockKey::new(stock_id, seed));
        self.shapes.insert(key, ShapeFiles { header: Some(header), journal: Some(journal), items: Some(items), count: 0 });
        Ok(stock_id)
    }

    /// Write item `index` (it must be the next one) with its agreed hash.
    pub fn put(&mut self, shape: &ShapeId, index: u64, bytes: &[u8], agreed: [u8; 32]) -> Result<(), StockError> {
        let boot_arc = Arc::clone(&self.boot);
        let mut boot = boot_arc.lock().expect("boot memory");
        let key = self.ensure(shape)?;
        let files = self.shapes.get_mut(&key).expect("loaded");
        let u = usable(files, &mut boot, &key)?;
        if u.next() > *u.count || u.key.prod_index != *u.count {
            return Err(StockError::Exhausted);
        }
        if index != *u.count {
            return Err(StockError::OutOfOrder);
        }
        if bytes.len() as u64 != u.header.item_len {
            return Err(StockError::BadLength);
        }
        // the key, and the producer chain moved past it, before anything is written
        let item_key = u.key.prod_chain.take_key(index).map_err(|_| StockError::Exhausted)?;
        u.key.prod_index = index + 1;
        let head = ItemHead { index, length: u.header.item_len, agreed };
        let sealed = self.cipher.seal(&item_key, &item_aad(u.header, &head), bytes);
        drop(item_key);
        let record = head.enc_item(&sealed);
        u.items.write_all_at(&record, index * u.header.record_len())?;
        u.items.sync_data()?;
        *u.count = index + 1;
        Ok(())
    }

    /// The next index this node may use for `shape` (its claim in the per-message agreement).
    pub fn next_index(&mut self, shape: &ShapeId) -> Result<u64, StockError> {
        let boot_arc = Arc::clone(&self.boot);
        let mut boot = boot_arc.lock().expect("boot memory");
        let key = self.ensure(shape)?;
        let files = self.shapes.get_mut(&key).expect("loaded");
        Ok(usable(files, &mut boot, &key)?.next())
    }

    /// The agreed hash stored with item `index` (read before the item is taken, to build the
    /// `stockUse` skeleton; authenticated only when the item is taken).
    pub fn agreed_hash(&mut self, shape: &ShapeId, index: u64) -> Result<[u8; 32], StockError> {
        let boot_arc = Arc::clone(&self.boot);
        let mut boot = boot_arc.lock().expect("boot memory");
        let key = self.ensure(shape)?;
        let files = self.shapes.get_mut(&key).expect("loaded");
        let u = usable(files, &mut boot, &key)?;
        if index >= *u.count {
            return Err(StockError::Absent);
        }
        let mut head = [0u8; crate::format::ITEM_HEAD_LEN];
        u.items.read_exact_at(&mut head, index * u.header.record_len())?;
        Ok(ItemHead::dec_head(&head).ok_or(StockError::Corrupt)?.agreed)
    }

    /// Skip forward to `index` (the peer is ahead): every index below it becomes unusable. Never
    /// back: an index at or below the next index changes nothing. Returns the next index.
    pub fn skip_to(&mut self, shape: &ShapeId, index: u64) -> Result<u64, StockError> {
        let boot_arc = Arc::clone(&self.boot);
        let mut boot = boot_arc.lock().expect("boot memory");
        let key = self.ensure(shape)?;
        let files = self.shapes.get_mut(&key).expect("loaded");
        let u = usable(files, &mut boot, &key)?;
        let next = u.next();
        if index <= next {
            return Ok(next);
        }
        u.journal.append(index - 1)?;
        u.journal.sync()?;
        u.key.advance_use(index, *u.count);
        Ok(index)
    }

    /// Take item `index`: journal and sync, erase its key, decrypt and verify.
    pub fn take(&mut self, shape: &ShapeId, index: u64) -> Result<Item, StockError> {
        self.take_inner(shape, index, None)
    }

    /// `take`, refusing BEFORE anything is consumed if the stored agreed hash is not `expected`
    /// (the hash both nodes put in the `stockUse` skeleton); the hash is verified again,
    /// authenticated, after decryption.
    pub fn take_expect(&mut self, shape: &ShapeId, index: u64, expected: &[u8; 32]) -> Result<Item, StockError> {
        self.take_inner(shape, index, Some(expected))
    }

    fn take_inner(&mut self, shape: &ShapeId, index: u64, expected: Option<&[u8; 32]>) -> Result<Item, StockError> {
        let boot_arc = Arc::clone(&self.boot);
        let mut boot = boot_arc.lock().expect("boot memory");
        let key = self.ensure(shape)?;
        #[cfg(test)]
        let cut_at = self.cut_at.take();
        let files = self.shapes.get_mut(&key).expect("loaded");
        let u = usable(files, &mut boot, &key)?;
        // 1. checks (Lean `start`)
        if index < u.next() {
            return Err(StockError::Behind);
        }
        if index >= *u.count {
            return Err(StockError::Absent);
        }
        let record_len = u.header.record_len();
        let mut record = vec![0u8; usize::try_from(record_len).map_err(|_| StockError::Corrupt)?];
        u.items.read_exact_at(&mut record, index * record_len)?;
        if let Some(e) = expected {
            if ItemHead::dec_head(&record).map(|h| h.agreed) != Some(*e) {
                return Err(StockError::WrongHash);
            }
        }
        // 2. journal, then fsync (Lean `start`, `sync`)
        u.journal.append(index)?;
        #[cfg(test)]
        if cut_at == Some(0) {
            return Err(StockError::Cut);
        }
        u.journal.sync()?;
        #[cfg(test)]
        if cut_at == Some(1) {
            return Err(StockError::Cut);
        }
        // 3. the key, and the use chain moved past it (Lean `decrypt`)
        if u.key.use_index > index {
            return Err(StockError::Erased);
        }
        let item_key = u.key.use_chain.take_key(index).map_err(|_| StockError::Erased)?;
        u.key.use_index = index + 1;
        #[cfg(test)]
        if cut_at == Some(2) {
            return Err(StockError::Cut);
        }
        // 4. decrypt and verify (Lean `hand`: the bytes go to the engine)
        let (head, sealed) = ItemHead::dec_item(&record).ok_or(StockError::Corrupt)?;
        if head.index != index || head.length != u.header.item_len {
            return Err(StockError::Corrupt);
        }
        if let Some(e) = expected {
            if head.agreed != *e {
                return Err(StockError::WrongHash);
            }
        }
        let bytes = self.cipher.open(&item_key, &item_aad(u.header, &head), &sealed).ok_or(StockError::Corrupt)?;
        Ok(Item { index, bytes, agreed: head.agreed })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cipher::{ChaChaCipher, NullCipher};
    use crate::journal::REC_LEN;

    pub(crate) fn scratch(name: &str) -> PathBuf {
        let d = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target").join("test-scratch").join(name);
        let _ = fs::remove_dir_all(&d);
        fs::create_dir_all(&d).unwrap();
        d
    }

    fn shape() -> ShapeId {
        ShapeId::new("signal-seal-official", 2, "official")
    }

    fn item(i: u64) -> Vec<u8> {
        (0..64u64).map(|k| (i * 31 + k * 7) as u8).collect()
    }

    fn agreed(i: u64) -> [u8; 32] {
        crate::format::sha256(&[b"agreed", &i.to_le_bytes()])
    }

    fn filled<C: ItemCipher>(dir: &Path, boot: &Arc<Mutex<BootMemory>>, cipher: C, n: u64) -> Store<C> {
        let mut s = Store::open(dir, Arc::clone(boot), cipher).unwrap();
        s.create(&shape(), 64, [7; 32]).unwrap();
        for i in 0..n {
            s.put(&shape(), i, &item(i), agreed(i)).unwrap();
        }
        s
    }

    #[test]
    fn take_in_order_and_never_twice() {
        let dir = scratch("order");
        let boot = Arc::new(Mutex::new(BootMemory::new().unwrap()));
        let mut s = filled(&dir, &boot, ChaChaCipher, 5);
        assert_eq!(s.next_index(&shape()).unwrap(), 0);
        let it = s.take(&shape(), 0).unwrap();
        assert_eq!(*it.bytes, item(0));
        assert_eq!(it.agreed, agreed(0));
        assert!(matches!(s.take(&shape(), 0), Err(StockError::Behind)));
        // skip forward (the peer is ahead), never back
        assert_eq!(s.skip_to(&shape(), 3).unwrap(), 3);
        assert_eq!(s.skip_to(&shape(), 1).unwrap(), 3);
        assert!(matches!(s.take(&shape(), 2), Err(StockError::Behind)));
        assert_eq!(*s.take(&shape(), 3).unwrap().bytes, item(3));
        assert!(matches!(s.take(&shape(), 5), Err(StockError::Absent)));
        // a crash (drop) and restart with the same boot memory: still never twice
        drop(s);
        let mut s = Store::open(&dir, Arc::clone(&boot), ChaChaCipher).unwrap();
        assert_eq!(s.next_index(&shape()).unwrap(), 4);
        for i in 0..4 {
            assert!(matches!(s.take(&shape(), i), Err(StockError::Behind)));
        }
        assert_eq!(*s.take(&shape(), 4).unwrap().bytes, item(4));
        // the items are encrypted on disk
        let raw = fs::read(dir.join(shape().dir_name()).join("items")).unwrap();
        assert!(!raw.windows(64).any(|w| w == item(1).as_slice()));
    }

    /// Crash at every point of the journal: truncate the file at every byte offset (including
    /// below what was synced, which a crash never does) and restart. No taken index can be taken
    /// again: at or above the synced length the journal alone refuses it; below it the erased
    /// key does (the chain barrier).
    #[test]
    fn journal_truncated_at_every_offset() {
        let dir = scratch("truncate");
        let boot = Arc::new(Mutex::new(BootMemory::new().unwrap()));
        let mut s = filled(&dir, &boot, NullCipher, 8);
        let taken = [0u64, 1, 3, 4, 6];
        for &i in &taken {
            if s.next_index(&shape()).unwrap() < i {
                s.skip_to(&shape(), i).unwrap();
            }
            s.take(&shape(), i).unwrap();
        }
        drop(s);
        let jpath = dir.join(shape().dir_name()).join("journal");
        let full = fs::read(&jpath).unwrap();
        let synced = full.len();
        for cut in 0..=synced {
            fs::write(&jpath, &full[..cut]).unwrap();
            let mut s = Store::open(&dir, Arc::clone(&boot), NullCipher).unwrap();
            let next = s.next_index(&shape()).unwrap();
            assert!(next >= 7, "the chain keeps next past every taken index (cut {cut})");
            for &i in &taken {
                assert!(s.take(&shape(), i).is_err(), "index {i} taken again after cut at {cut}");
            }
            // the restart truncated a torn tail to whole records
            assert_eq!(fs::metadata(&jpath).unwrap().len() as usize % REC_LEN, 0);
            drop(s);
        }
        // the journal alone (a fresh boot memory with the same stock key state would be a
        // rollback; here: the journal's own next index at each synced-or-longer cut)
        for cut in (synced - synced % REC_LEN)..=synced {
            let es = crate::journal::parse(&read_stock_id(&dir), &full[..cut]).unwrap();
            assert!(taken.iter().all(|&i| i < crate::journal::next_of(&es)));
        }
    }

    fn read_stock_id(dir: &Path) -> [u8; 32] {
        let h = Header::parse(&fs::read(dir.join(shape().dir_name()).join("header")).unwrap()).unwrap();
        h.stock_id
    }

    /// A crash between the journal append and its fsync, keeping any number of the unsynced
    /// bytes: the item in flight is either consumed or not, never handed twice.
    #[test]
    fn cut_take_then_crash() {
        for step in 0..3u8 {
            for keep in 0..=REC_LEN {
                let dir = scratch(&format!("cut-{step}-{keep}"));
                let boot = Arc::new(Mutex::new(BootMemory::new().unwrap()));
                let mut s = filled(&dir, &boot, ChaChaCipher, 4);
                s.take(&shape(), 0).unwrap();
                s.cut_at = Some(step);
                assert!(matches!(s.take(&shape(), 1), Err(StockError::Cut)));
                drop(s);
                let jpath = dir.join(shape().dir_name()).join("journal");
                let full = fs::read(&jpath).unwrap();
                let durable = if step == 0 { full.len() - REC_LEN } else { full.len() };
                fs::write(&jpath, &full[..durable + keep.min(full.len() - durable)]).unwrap();
                let mut s = Store::open(&dir, Arc::clone(&boot), ChaChaCipher).unwrap();
                let next = s.next_index(&shape()).unwrap();
                let expect = if step >= 2 || step == 1 || keep >= REC_LEN { 2 } else { 1 };
                assert_eq!(next, expect, "step {step} keep {keep}");
                assert!(matches!(s.take(&shape(), 0), Err(StockError::Behind)));
                if next == 1 {
                    // the entry was lost and the key not erased: item 1 was never handed; it may
                    // be used now, once
                    assert_eq!(*s.take(&shape(), 1).unwrap().bytes, item(1));
                }
                assert!(s.take(&shape(), 1).is_err());
                assert_eq!(*s.take(&shape(), 2).unwrap().bytes, item(2));
            }
        }
    }

    #[test]
    fn other_boot_is_unusable() {
        let dir = scratch("boot");
        let boot = Arc::new(Mutex::new(BootMemory::new().unwrap()));
        let mut s = filled(&dir, &boot, ChaChaCipher, 3);
        s.take(&shape(), 0).unwrap();
        drop(s);
        // a reboot: new boot memory, the same disk
        let boot2 = Arc::new(Mutex::new(BootMemory::new().unwrap()));
        let mut s = Store::open(&dir, Arc::clone(&boot2), ChaChaCipher).unwrap();
        assert!(matches!(s.next_index(&shape()), Err(StockError::Unusable)));
        assert!(matches!(s.take(&shape(), 1), Err(StockError::Unusable)));
        assert!(matches!(s.put(&shape(), 3, &item(3), agreed(3)), Err(StockError::Unusable)));
        assert!(matches!(s.skip_to(&shape(), 2), Err(StockError::Unusable)));
        // even with a header rewritten to carry the new boot id, the key is not in boot memory
        let hpath = dir.join(shape().dir_name()).join("header");
        let mut h = Header::parse(&fs::read(&hpath).unwrap()).unwrap();
        h.boot_id = boot2.lock().unwrap().boot_id();
        fs::write(&hpath, h.enc()).unwrap();
        let mut s = Store::open(&dir, Arc::clone(&boot2), ChaChaCipher).unwrap();
        assert!(matches!(s.take(&shape(), 1), Err(StockError::Unusable)));
    }

    /// A disk restored from a snapshot taken in the same boot: the journal is older, the chain
    /// is not, so the used item stays unusable.
    #[test]
    fn same_boot_disk_restore() {
        let dir = scratch("restore");
        let boot = Arc::new(Mutex::new(BootMemory::new().unwrap()));
        let mut s = filled(&dir, &boot, ChaChaCipher, 3);
        let d = dir.join(shape().dir_name());
        let snap: Vec<(String, Vec<u8>)> =
            ["header", "items", "journal"].iter().map(|n| (n.to_string(), fs::read(d.join(n)).unwrap())).collect();
        s.take(&shape(), 0).unwrap();
        drop(s);
        for (n, b) in &snap {
            fs::write(d.join(n), b).unwrap();
        }
        let mut s = Store::open(&dir, Arc::clone(&boot), ChaChaCipher).unwrap();
        assert_eq!(s.next_index(&shape()).unwrap(), 1);
        assert!(s.take(&shape(), 0).is_err());
    }

    #[test]
    fn wrong_item_hash() {
        let dir = scratch("hash");
        let boot = Arc::new(Mutex::new(BootMemory::new().unwrap()));
        let mut s = filled(&dir, &boot, ChaChaCipher, 3);
        // a different expected hash: refused before anything is consumed
        assert!(matches!(s.take_expect(&shape(), 0, &[0; 32]), Err(StockError::WrongHash)));
        assert_eq!(s.next_index(&shape()).unwrap(), 0);
        assert_eq!(s.agreed_hash(&shape(), 0).unwrap(), agreed(0));
        assert_eq!(*s.take_expect(&shape(), 0, &agreed(0)).unwrap().bytes, item(0));
        // the stored hash tampered to match a wrong expectation: the early check passes, the
        // authenticated one fails; the index is consumed and never handed
        drop(s);
        let ipath = dir.join(shape().dir_name()).join("items");
        let mut raw = fs::read(&ipath).unwrap();
        let rl = crate::format::record_len(64) as usize;
        raw[rl + 16..rl + 48].copy_from_slice(&[5; 32]);
        fs::write(&ipath, &raw).unwrap();
        let mut s = Store::open(&dir, Arc::clone(&boot), ChaChaCipher).unwrap();
        assert!(matches!(s.take_expect(&shape(), 1, &[5; 32]), Err(StockError::Corrupt)));
        assert_eq!(s.next_index(&shape()).unwrap(), 2);
        assert!(matches!(s.take(&shape(), 1), Err(StockError::Behind)));
        // a tampered ciphertext byte
        drop(s);
        let mut raw = fs::read(&ipath).unwrap();
        raw[2 * rl + 60] ^= 1;
        fs::write(&ipath, &raw).unwrap();
        let mut s = Store::open(&dir, Arc::clone(&boot), ChaChaCipher).unwrap();
        assert!(matches!(s.take(&shape(), 2), Err(StockError::Corrupt)));
    }

    /// Items are bound to their index: a record copied to another index does not open there.
    #[test]
    fn records_bound_to_index() {
        let dir = scratch("swap");
        let boot = Arc::new(Mutex::new(BootMemory::new().unwrap()));
        let s = filled(&dir, &boot, NullCipher, 3);
        drop(s);
        let ipath = dir.join(shape().dir_name()).join("items");
        let mut raw = fs::read(&ipath).unwrap();
        let rl = crate::format::record_len(64) as usize;
        let r2 = raw[2 * rl..3 * rl].to_vec();
        raw[rl..2 * rl].copy_from_slice(&r2);
        fs::write(&ipath, &raw).unwrap();
        let mut s = Store::open(&dir, Arc::clone(&boot), NullCipher).unwrap();
        assert!(matches!(s.take(&shape(), 1), Err(StockError::Corrupt)));
    }

    #[test]
    fn put_rules() {
        let dir = scratch("put");
        let boot = Arc::new(Mutex::new(BootMemory::new().unwrap()));
        let mut s = filled(&dir, &boot, ChaChaCipher, 2);
        assert!(matches!(s.put(&shape(), 3, &item(3), agreed(3)), Err(StockError::OutOfOrder)));
        assert!(matches!(s.put(&shape(), 2, &item(2)[..10], agreed(2)), Err(StockError::BadLength)));
        s.put(&shape(), 2, &item(2), agreed(2)).unwrap();
        // the peer pushes us past the end: the stock takes no more items
        assert_eq!(s.skip_to(&shape(), 10).unwrap(), 10);
        assert!(matches!(s.put(&shape(), 3, &item(3), agreed(3)), Err(StockError::Exhausted)));
        assert!(matches!(s.take(&shape(), 10), Err(StockError::Absent)));
        // a new stock replaces it
        s.create(&shape(), 64, [7; 32]).unwrap();
        s.put(&shape(), 0, &item(0), agreed(0)).unwrap();
        assert_eq!(*s.take(&shape(), 0).unwrap().bytes, item(0));
    }
}
