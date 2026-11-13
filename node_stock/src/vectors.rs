//! The Rust store against the Lean model: `tests/stock_vectors.txt`, printed by
//! `tests/lean/StockVectors.lean` from TlsMpc/Node/Stock/Format.lean and Use.lean (regenerate with
//! `python3 .deps/lowering-scratch/x1_vectors.py`). The format lines must match byte for byte; the
//! schedules (hand-written ones and 300 generated from the model: takes at, behind and ahead of
//! the next index, far ahead as a lying peer would ask, takes cut at every step followed by a crash
//! keeping any number of unsynced journal bytes, skips, crashes, reboots, new stocks, refills, disk
//! and boot-memory snapshots restored) must give the same outcome and the same next index after
//! every operation, and hand the same items.

use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;
use std::sync::{Arc, Mutex};

use crate::boot::{BootMemory, StockKey};
use crate::chain::Chain;
use crate::cipher::ChaChaCipher;
use crate::format::{Header, ItemHead, ShapeId, enc_claim, enc_stock_use, hex, item_aad, item_key, unhex};
use crate::journal::{REC_LEN, enc_rec, parse};
use crate::store::{StockError, Store};

const VECTORS: &str = include_str!("../tests/stock_vectors.txt");

fn bytes_from(start: u64, n: u64) -> Vec<u8> {
    (0..n).map(|k| (start + k) as u8).collect()
}

fn arr(v: Vec<u8>) -> [u8; 32] {
    v.try_into().expect("32 bytes")
}

fn shape_a() -> ShapeId {
    ShapeId::new("signal-seal-official", 3, "official")
}

fn header_a() -> Header {
    Header {
        shape: shape_a(),
        manifest: arr(bytes_from(0, 32)),
        boot_id: arr(bytes_from(100, 32)),
        stock_id: arr(bytes_from(200, 32)),
        item_len: 40,
    }
}

fn head_of(i: u64) -> ItemHead {
    ItemHead { index: i, length: 40, agreed: arr(bytes_from(i * 3, 32)) }
}

#[test]
fn format_vectors() {
    let mut checked = 0;
    for line in VECTORS.lines() {
        let f: Vec<&str> = line.split(' ').collect();
        match f[0] {
            "sha256-abc" => assert_eq!(hex(&crate::format::sha256(&[b"abc"])), f[1]),
            "shape" => assert_eq!(hex(&shape_a().enc()), f[1]),
            "header" => {
                assert_eq!(hex(&header_a().enc()), f[1]);
                assert_eq!(Header::parse(&unhex(f[1]).unwrap()), Some(header_a()));
            }
            "item" => {
                let i: u64 = f[1].parse().unwrap();
                let rec = head_of(i).enc_item(&bytes_from(9, 56));
                assert_eq!(hex(&rec), f[2], "item {i}");
                assert_eq!(ItemHead::dec_item(&rec), Some((head_of(i), bytes_from(9, 56))));
            }
            "aad" => {
                let i: u64 = f[1].parse().unwrap();
                assert_eq!(hex(&item_aad(&header_a(), &head_of(i))), f[2], "aad {i}");
            }
            "jrec" => {
                let stock = arr(unhex(f[1]).unwrap());
                let w: u64 = f[2].parse().unwrap();
                assert_eq!(hex(&enc_rec(&stock, w)), f[3], "jrec {w}");
            }
            "jparse" => {
                let stock = arr(unhex(f[1]).unwrap());
                let n: usize = f[2].parse().unwrap();
                let file = unhex(f[3]).unwrap();
                let got = match parse(&stock, &file[..n.min(file.len())]) {
                    Ok(es) if es.is_empty() => "-".to_string(),
                    Ok(es) => es.iter().map(|e| e.to_string()).collect::<Vec<_>>().join(","),
                    Err(_) => "corrupt".to_string(),
                };
                assert_eq!(got, f[4], "jparse at {n}");
            }
            "chain" => {
                let mut seed = arr(unhex(f[1]).unwrap());
                let i: u64 = f[2].parse().unwrap();
                let mut c = seed;
                for _ in 0..i {
                    c = crate::format::chain_next(&c);
                }
                assert_eq!(hex(&c), f[3]);
                assert_eq!(hex(&item_key(&c)), f[4]);
                let mut ch = Chain::from_seed(&mut seed);
                assert_eq!(hex(&*ch.take_key(i).unwrap()), f[4]);
            }
            "claim" => {
                let c = if f[1] == "none" { None } else { Some(f[1].parse().unwrap()) };
                assert_eq!(hex(&enc_claim(c)), f[2]);
            }
            "stockuse" => {
                let i: u64 = f[1].parse().unwrap();
                assert_eq!(hex(&enc_stock_use(&shape_a(), i, &arr(bytes_from(1, 32)))), f[2]);
            }
            _ => continue,
        }
        checked += 1;
    }
    assert!(checked >= 38, "format lines checked: {checked}");
}

fn item(i: u64) -> Vec<u8> {
    (0..40u64).map(|k| (i.wrapping_mul(131) ^ k.wrapping_mul(29)) as u8).collect()
}

fn agreed(i: u64) -> [u8; 32] {
    crate::format::sha256(&[b"vector item", &i.to_le_bytes()])
}

type DiskSnap = Vec<(&'static str, Option<Vec<u8>>)>;

struct Harness {
    dir: PathBuf,
    boot: Arc<Mutex<BootMemory>>,
    store: Option<Store<ChaChaCipher>>,
    disk_snaps: Vec<DiskSnap>,
    boot_snaps: Vec<Option<StockKey>>,
    handed: Vec<u64>,
}

impl Harness {
    fn new(name: &str) -> Harness {
        let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target").join("test-scratch").join(name);
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        let boot = Arc::new(Mutex::new(BootMemory::new().unwrap()));
        let store = Some(Store::open(&dir, Arc::clone(&boot), ChaChaCipher).unwrap());
        Harness { dir, boot, store, disk_snaps: Vec::new(), boot_snaps: Vec::new(), handed: Vec::new() }
    }

    fn shape() -> ShapeId {
        ShapeId::new("x1-vectors", 1, "test")
    }

    fn shape_dir(&self) -> PathBuf {
        self.dir.join(Self::shape().dir_name())
    }

    fn st(&mut self) -> &mut Store<ChaChaCipher> {
        self.store.as_mut().expect("store open")
    }

    /// A crash of the process: drop the store; the journal keeps its synced bytes and `keep` of
    /// the `unsynced` ones; restart with the same boot memory.
    fn crash(&mut self, unsynced: usize, keep: usize) {
        self.store = None;
        let j = self.shape_dir().join("journal");
        if let Ok(b) = fs::read(&j) {
            let durable = b.len() - unsynced;
            fs::write(&j, &b[..durable + keep.min(unsynced)]).unwrap();
        }
        self.store = Some(Store::open(&self.dir, Arc::clone(&self.boot), ChaChaCipher).unwrap());
    }

    fn refusal(e: StockError) -> String {
        format!("refused {}", e.name())
    }

    fn op(&mut self, args: &[&str]) -> String {
        let sh = Self::shape();
        let n = |k: usize| -> u64 { args[k].parse().unwrap() };
        match args[0] {
            "create" => {
                self.st().create(&sh, 40, [7; 32]).unwrap();
                "ok".into()
            }
            "put" => {
                // Lean `extend k`: the next k indices
                let k = n(1);
                if let Err(e) = self.st().next_index(&sh) {
                    return Self::refusal(e);
                }
                let start = self.count();
                for m in 0..k {
                    if let Err(e) = self.st().put(&sh, start + m, &item(start + m), agreed(start + m)) {
                        assert_eq!(m, 0, "a refill refused part way");
                        return Self::refusal(e);
                    }
                }
                "ok".into()
            }
            "take" => match self.st().take(&sh, n(1)) {
                Ok(it) => {
                    assert_eq!(*it.bytes, item(n(1)));
                    assert_eq!(it.agreed, agreed(n(1)));
                    self.handed.push(n(1));
                    format!("handed {}", n(1))
                }
                Err(e) => Self::refusal(e),
            },
            "cut" => {
                let (j, step, keep) = (n(1), n(2) as u8, n(3) as usize);
                self.st().cut_at = Some(step);
                let (out, unsynced) = match self.st().take(&sh, j) {
                    Ok(_) => panic!("a cut take returned an item"),
                    Err(StockError::Cut) => ("cut".to_string(), if step == 0 { REC_LEN } else { 0 }),
                    Err(e) => (Self::refusal(e), 0),
                };
                self.crash(unsynced, keep);
                out
            }
            "skip" => match self.st().skip_to(&sh, n(1)) {
                Ok(_) => "ok".into(),
                Err(e) => Self::refusal(e),
            },
            "crash" => {
                self.crash(0, n(1) as usize);
                "ok".into()
            }
            "reboot" => {
                self.store = None;
                self.boot = Arc::new(Mutex::new(BootMemory::new().unwrap()));
                self.boot_snaps.clear();
                self.crash(0, n(1) as usize);
                "ok".into()
            }
            "snapdisk" => {
                let d = self.shape_dir();
                let snap = ["header", "items", "journal"].iter().map(|f| (*f, fs::read(d.join(f)).ok())).collect();
                self.disk_snaps.push(snap);
                "ok".into()
            }
            "restoredisk" => {
                self.store = None;
                let d = self.shape_dir();
                fs::create_dir_all(&d).unwrap();
                for (f, b) in self.disk_snaps[n(1) as usize].clone() {
                    match b {
                        Some(b) => fs::write(d.join(f), b).unwrap(),
                        None => {
                            let _ = fs::remove_file(d.join(f));
                        }
                    }
                }
                self.crash(0, 0);
                "ok".into()
            }
            "snapboot" => {
                let k = self.boot.lock().unwrap().shapes.get(&sh.key()).map(|k| k.duplicate());
                self.boot_snaps.push(k);
                "ok".into()
            }
            "restoreboot" => {
                self.store = None;
                let k = self.boot_snaps[n(1) as usize].as_ref().map(|k| k.duplicate());
                {
                    let mut b = self.boot.lock().unwrap();
                    match k {
                        Some(k) => {
                            b.shapes.insert(sh.key(), k);
                        }
                        None => {
                            b.shapes.remove(&sh.key());
                        }
                    }
                }
                self.crash(0, 0);
                "ok".into()
            }
            other => panic!("unknown op {other}"),
        }
    }

    /// The number of items on disk (the next index a refill writes).
    fn count(&self) -> u64 {
        let d = self.shape_dir();
        let Ok(m) = fs::metadata(d.join("items")) else { return 0 };
        m.len() / crate::format::record_len(40)
    }

    fn next(&mut self) -> String {
        match self.st().next_index(&Self::shape()) {
            Ok(n) => n.to_string(),
            Err(StockError::Unusable) => "-".into(),
            Err(e) => panic!("next_index: {e:?}"),
        }
    }
}

#[test]
fn schedules_agree_with_lean() {
    let mut schedules = 0;
    let mut ops = 0;
    let mut outcomes: HashMap<String, usize> = HashMap::new();
    let mut h: Option<Harness> = None;
    let mut name = String::new();
    let mut dups = 0;
    for line in VECTORS.lines() {
        if let Some(rest) = line.strip_prefix("schedule ") {
            name = rest.to_string();
            h = Some(Harness::new(&format!("vec-{rest}")));
            schedules += 1;
        } else if let Some(rest) = line.strip_prefix("op ") {
            let parts: Vec<&str> = rest.split(" | ").collect();
            let args: Vec<&str> = parts[0].split(' ').collect();
            let hh = h.as_mut().expect("in a schedule");
            let out = hh.op(&args);
            let next = hh.next();
            assert_eq!((out.as_str(), next.as_str()), (parts[1], parts[2]), "schedule {name}, op {}", parts[0]);
            *outcomes.entry(parts[1].split(' ').next().unwrap().to_string()).or_default() += 1;
            ops += 1;
        } else if let Some(rest) = line.strip_prefix("handed ") {
            let hh = h.as_ref().expect("in a schedule");
            let got = if hh.handed.is_empty() {
                "-".to_string()
            } else {
                hh.handed.iter().map(|e| e.to_string()).collect::<Vec<_>>().join(",")
            };
            assert_eq!(got, rest, "schedule {name}: handed");
        } else if line == "nodup no" {
            dups += 1;
        } else if line == "end" {
            let hh = h.take().expect("in a schedule");
            let _ = fs::remove_dir_all(&hh.dir);
        }
    }
    eprintln!("lean vectors: {schedules} schedules, {ops} operations, outcomes {outcomes:?}, {dups} schedules with a full rollback reuse");
    assert!(schedules >= 300 && ops > 5000);
}
