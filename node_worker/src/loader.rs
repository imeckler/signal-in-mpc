//! Strict-mode circuit loading (`kernel.h` `KernelCache`, lines 85-174; CIRCUIT_SHAPES.md).
//!
//! `CIRCUIT_MANIFEST` names the `manifest.txt` written by scripts/produce_circuits.py. Only the
//! kernels it lists exist, read from its directory and checked against its pins; nothing is
//! ever produced (no interpreter, no emitter). The two workers compare the manifest's SHA-256 on
//! the control link at start, before any request.
//!
//! The production worker requires a manifest. The `test-engine` build alone may run without one
//! (development fixtures; the C++ library then produces kernels on demand through the cache
//! script, as the C++ worker does).
//!
//! In S8 the engines still load each kernel themselves (the legacy library's `KernelCache`, in
//! strict mode from the same variable, re-checking every pin). What this module adds: the
//! manifest is parsed and every listed file is checked to exist and every layout to match its
//! pin before the session starts, and the manifest agreement happens before the first request.
use crate::handles::{Mark, Sig};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

pub const MANIFEST_FORMAT: &str = "EMP_HYBRID_CIRCUIT_MANIFEST_V1";

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pinned {
    pub sha256: String,
    pub layout_sha256: String,
}

#[derive(Debug, Clone)]
pub struct Manifest {
    pub directory: PathBuf,
    pub digest: [u8; 32],
    pub kernels: BTreeMap<String, Pinned>,
}

fn hex64(s: &str) -> bool {
    s.len() == 64 && s.bytes().all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c))
}

pub fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// File stem of a kernel: "kernel-" and its arguments, spaces as dashes.
pub fn stem(arguments: &str) -> String {
    format!("kernel-{}", arguments.replace(' ', "-"))
}

impl Manifest {
    /// Parses a manifest's text: the format line, then rows `SHA256 LAYOUT_SHA256 NAME [PARAMETERS]`
    /// with single spaces; names of letters, digits, '-' and ' '; no name twice.
    pub fn parse(text: &[u8], directory: PathBuf) -> Result<Manifest, String> {
        let digest: [u8; 32] = Sha256::digest(text).into();
        let text = std::str::from_utf8(text).map_err(|_| "circuit manifest row")?;
        let mut lines = text.split('\n');
        if lines.next() != Some(MANIFEST_FORMAT) {
            return Err("circuit manifest format".into());
        }
        let mut kernels = BTreeMap::new();
        let rows: Vec<&str> = lines.collect();
        // A final newline ends the last row (std::getline yields no empty last line for it).
        let rows = match rows.split_last() {
            Some((&"", rest)) => rest,
            _ => &rows[..],
        };
        for line in rows {
            let b = line.as_bytes();
            if b.len() < 131 || b[64] != b' ' || b[129] != b' ' {
                return Err("circuit manifest row".into());
            }
            let (sha, layout, name) = (&line[..64], &line[65..129], &line[130..]);
            if !name.bytes().all(|c| c.is_ascii_alphanumeric() || c == b'-' || c == b' ') || !hex64(sha) || !hex64(layout) {
                return Err("circuit manifest row".into());
            }
            let pinned = Pinned { sha256: sha.to_string(), layout_sha256: layout.to_string() };
            if kernels.insert(name.to_string(), pinned).is_some() {
                return Err("circuit manifest row".into());
            }
        }
        Ok(Manifest { directory, digest, kernels })
    }

    pub fn load(path: &Path) -> Result<Manifest, String> {
        let text = std::fs::read(path).map_err(|_| "circuit manifest file")?;
        let directory = path.parent().map(Path::to_path_buf).unwrap_or_default();
        Self::parse(&text, directory)
    }

    pub fn flat_path(&self, arguments: &str) -> PathBuf {
        self.directory.join(format!("{}.flat", stem(arguments)))
    }
    pub fn layout_path(&self, arguments: &str) -> PathBuf {
        self.directory.join(format!("{}.layout", stem(arguments)))
    }

    /// Every listed flat file exists and every layout matches its pin. (The flat files, up to
    /// hundreds of MB each, are hashed by the engines when they load them.)
    pub fn check_files(&self) -> Result<(), String> {
        for (name, pinned) in &self.kernels {
            if !self.flat_path(name).is_file() {
                return Err(format!("circuit manifest: missing {}", self.flat_path(name).display()));
            }
            let layout = std::fs::read(self.layout_path(name)).map_err(|_| format!("circuit manifest: missing layout of {name}"))?;
            if hex(&Sha256::digest(&layout)) != pinned.layout_sha256 {
                return Err(format!("kernel layout pin: {name}"));
            }
        }
        Ok(())
    }
}

pub const LAYOUT_FORMAT: &str = "EMP_HYBRID_KERNEL_LAYOUT_V1";

/// A kernel layout's signature for `check` (Lean `Sig`): the input width of one copy (the sum
/// of its `I` rows) and the output marks of one copy (each `O` row's mark repeated over its bits),
/// read as `kernel.h` `Kernel` reads the layout (rows `I NAME BITS` / `O NAME BITS OPENED`,
/// whitespace-separated, OPENED 0..3).
pub fn parse_layout(text: &[u8]) -> Result<Sig, String> {
    let text = std::str::from_utf8(text).map_err(|_| "kernel layout row")?;
    let mut lines = text.lines();
    if lines.next() != Some(LAYOUT_FORMAT) {
        return Err("kernel layout format".into());
    }
    let mut sig = Sig { in_width: 0, out_marks: Vec::new() };
    for line in lines {
        let row: Vec<&str> = line.split_whitespace().collect();
        let bits = row.get(2).and_then(|b| b.parse::<u64>().ok()).ok_or("kernel layout row")?;
        match (row.first().copied(), row.len()) {
            (Some("I"), 3) => sig.in_width = sig.in_width.checked_add(bits).ok_or("kernel layout row")?,
            (Some("O"), 4) => {
                let mark = row[3].parse::<u8>().ok().and_then(Mark::of_layout).ok_or("kernel layout row")?;
                if sig.out_marks.len() as u64 + bits > crate::handles::MAX_WIDTH {
                    return Err("kernel layout width".into());
                }
                sig.out_marks.extend(std::iter::repeat_n(mark, bits as usize));
            }
            _ => return Err("kernel layout row".into()),
        }
    }
    Ok(sig)
}

/// A kernel the interpreter can run: its flat file, the file's pin, and its signature.
#[derive(Debug, Clone, PartialEq)]
pub struct Kernel {
    pub flat: PathBuf,
    pub sha256: String,
    pub sig: Sig,
}

/// The kernels of `run` (interp.rs), by name (the manifest's NAME [PARAMETERS], as bytes): every
/// kernel of the manifest, none without one.
#[derive(Debug, Clone, Default)]
pub struct Kernels {
    entries: BTreeMap<Vec<u8>, Kernel>,
}

impl Kernels {
    /// Every manifest kernel, its layout read again and checked against its pin.
    pub fn from_manifest(m: &Manifest) -> Result<Kernels, String> {
        let mut entries = BTreeMap::new();
        for (name, pinned) in &m.kernels {
            let layout = std::fs::read(m.layout_path(name)).map_err(|_| format!("circuit manifest: missing layout of {name}"))?;
            if hex(&Sha256::digest(&layout)) != pinned.layout_sha256 {
                return Err(format!("kernel layout pin: {name}"));
            }
            let sig = parse_layout(&layout).map_err(|e| format!("{e}: {name}"))?;
            entries.insert(name.as_bytes().to_vec(), Kernel { flat: m.flat_path(name), sha256: pinned.sha256.clone(), sig });
        }
        Ok(Kernels { entries })
    }
    pub fn insert(&mut self, name: &[u8], kernel: Kernel) {
        self.entries.insert(name.to_vec(), kernel);
    }
    pub fn get(&self, name: &[u8]) -> Option<&Kernel> {
        self.entries.get(name)
    }
    /// Lean `sigs`.
    pub fn sig(&self, name: &[u8]) -> Option<Sig> {
        self.get(name).map(|k| k.sig.clone())
    }
}

/// A Lean word circuit outside the kernel manifest, which the engines load from its own pinned
/// file exactly as the legacy library does (`word_mask.h` line 27: `LeanCircuit{
/// EMP_WORD_CIRCUIT_DIR "/xor-bit.flat", WORD_XOR_BIT_SHA}`; `ea_circuit_load` builds the same
/// `LeanCircuit(path, sha)`, so no ABI change is involved). Its pin is `word_circuit_pins.h`'s
/// (written by lower_word_circuits.py from `TlsMpc/WordMask.lean`); it has no layout file, so its
/// signature for `check` is fixed here, next to the pin.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WordCircuit {
    /// The name a batch's `run` uses.
    pub name: &'static str,
    pub file: &'static str,
    pub sha256: &'static str,
    /// Lean `Sig`: input bits and output marks of one copy.
    pub in_width: u64,
    pub out_marks: &'static [Mark],
}

/// The word circuits `run` may name. `xor-bit`: one XOR gate, inputs (a, b), output a ⊕ b,
/// private (op 54 combines the two credential shares with 8·38 copies on the interleaved
/// shares, Account.lean `combineBlock`).
pub const WORD_CIRCUITS: &[WordCircuit] = &[WordCircuit {
    name: "xor-bit",
    file: "xor-bit.flat",
    sha256: "6495137f2dc968d4553b3560a5e09d4a1cdc182503460dbb0773783f35feadac",
    in_width: 2,
    out_marks: &[Mark::Never],
}];

/// The directory of the pinned word circuits: the engine library's `EMP_WORD_CIRCUIT_DIR`
/// (build_hybrid_v3.py: `.deps/emp-hybrid-word-v1`), or `NODE_WORKER_WORD_DIR` at build time.
pub fn word_circuit_dir() -> PathBuf {
    match option_env!("NODE_WORKER_WORD_DIR") {
        Some(d) => PathBuf::from(d),
        None => Path::new(env!("CARGO_MANIFEST_DIR")).join("../.deps/emp-hybrid-word-v1"),
    }
}

impl Kernels {
    /// Adds every word circuit whose file is in `dir`, after checking the file against its pin
    /// (the engine checks it again when it loads it). A file present with another hash, or a
    /// name the manifest already uses, is an error; an absent file is not added (then `check`
    /// refuses a `run` of it). Returns the names added, which the start agreement covers
    /// ([`agreement_digest`]).
    pub fn add_word_circuits(&mut self, dir: &Path) -> Result<Vec<&'static str>, String> {
        let mut added = Vec::new();
        for w in WORD_CIRCUITS {
            let flat = dir.join(w.file);
            let Ok(bytes) = std::fs::read(&flat) else { continue };
            if hex(&Sha256::digest(&bytes)) != w.sha256 {
                return Err(format!("word circuit pin: {}", w.name));
            }
            if self.get(w.name.as_bytes()).is_some() {
                return Err(format!("word circuit name in the manifest: {}", w.name));
            }
            let sig = Sig { in_width: w.in_width, out_marks: w.out_marks.to_vec() };
            self.insert(w.name.as_bytes(), Kernel { flat, sha256: w.sha256.to_string(), sig });
            added.push(w.name);
        }
        Ok(added)
    }
}

/// What the two workers compare at start: the circuit source's digest ([`Circuits::digest`])
/// alone when no word circuit is runnable, otherwise SHA-256 of it and each added word circuit's
/// name and pin, so two workers that could run different circuit sets stop before any request.
pub fn agreement_digest(circuits: &Circuits, words: &[&str]) -> [u8; 32] {
    if words.is_empty() {
        return circuits.digest();
    }
    let mut h = Sha256::new();
    h.update(circuits.digest());
    for name in words {
        let w = WORD_CIRCUITS.iter().find(|w| w.name == *name).expect("a listed word circuit");
        h.update(format!("\nword {} {}", w.name, w.sha256).as_bytes());
    }
    h.finalize().into()
}

/// The circuit source of this worker: a manifest, or (test-engine only) none.
#[derive(Debug, Clone)]
pub enum Circuits {
    Pinned(Manifest),
    Unpinned,
}

impl Circuits {
    /// From `CIRCUIT_MANIFEST` (unset or empty: no manifest). `allow_unpinned` is the
    /// test-engine build's.
    pub fn from_environment(value: Option<String>, allow_unpinned: bool) -> Result<Circuits, String> {
        match value.filter(|v| !v.is_empty()) {
            Some(path) => {
                let manifest = Manifest::load(Path::new(&path))?;
                manifest.check_files()?;
                Ok(Circuits::Pinned(manifest))
            }
            None if allow_unpinned => Ok(Circuits::Unpinned),
            None => Err("strict circuit loading required: CIRCUIT_MANIFEST is not set".into()),
        }
    }
    /// What the workers compare at start: the manifest's SHA-256, or zeros without one (so a
    /// pinned worker and an unpinned one never agree).
    pub fn digest(&self) -> [u8; 32] {
        match self {
            Circuits::Pinned(m) => m.digest,
            Circuits::Unpinned => [0; 32],
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn row(sha: char, layout: char, name: &str) -> String {
        format!("{} {} {name}", sha.to_string().repeat(64), layout.to_string().repeat(64))
    }

    #[test]
    fn parses_rows_and_hashes_the_whole_text() {
        let text = format!("{MANIFEST_FORMAT}\n{}\n{}\n", row('a', 'b', "tls-derive"), row('c', 'd', "tls-open-typed 48"));
        let m = Manifest::parse(text.as_bytes(), PathBuf::from("/m")).unwrap();
        assert_eq!(m.kernels.len(), 2);
        assert_eq!(m.kernels["tls-open-typed 48"].sha256, "c".repeat(64));
        assert_eq!(m.digest, <[u8; 32]>::from(Sha256::digest(text.as_bytes())));
        assert_eq!(m.flat_path("tls-open-typed 48"), PathBuf::from("/m/kernel-tls-open-typed-48.flat"));
    }

    #[test]
    fn refuses_malformed_manifests() {
        let bad = [
            format!("OTHER\n{}\n", row('a', 'b', "k")),
            format!("{MANIFEST_FORMAT}\n{}\n{}\n", row('a', 'b', "k"), row('c', 'd', "k")),
            format!("{MANIFEST_FORMAT}\n{}\n", row('A', 'b', "k")),
            format!("{MANIFEST_FORMAT}\n{}\n", row('a', 'b', "k/../x")),
            format!("{MANIFEST_FORMAT}\n{}\n", row('a', 'b', "")),
            format!("{MANIFEST_FORMAT}\n\n"),
        ];
        for text in bad {
            assert!(Manifest::parse(text.as_bytes(), PathBuf::new()).is_err(), "{text:?}");
        }
        assert!(Manifest::parse(format!("{MANIFEST_FORMAT}\n").as_bytes(), PathBuf::new()).unwrap().kernels.is_empty());
    }

    #[test]
    fn layout_signatures() {
        let text = format!("{LAYOUT_FORMAT}\nI length 16\nI content 56\nI none 0\nO length 2 1\nO a 1 2\nO b 1 3\nO hidden 2 0\n");
        let sig = parse_layout(text.as_bytes()).unwrap();
        assert_eq!(sig.in_width, 72);
        use Mark::*;
        assert_eq!(sig.out_marks, vec![Pub, Pub, ToA, ToB, Never, Never]);
        for bad in ["OTHER\n", "EMP_HYBRID_KERNEL_LAYOUT_V1\nO x 1 4\n", "EMP_HYBRID_KERNEL_LAYOUT_V1\nI x\n", "EMP_HYBRID_KERNEL_LAYOUT_V1\n\n", "EMP_HYBRID_KERNEL_LAYOUT_V1\nX x 1\n"] {
            assert!(parse_layout(bad.as_bytes()).is_err(), "{bad:?}");
        }
    }

    #[test]
    fn word_circuits_are_pinned() {
        let dir = std::env::temp_dir().join(format!("node-worker-words-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        // Absent: not added.
        let mut k = Kernels::default();
        assert_eq!(k.add_word_circuits(&dir).unwrap(), Vec::<&str>::new());
        assert!(k.sig(b"xor-bit").is_none());
        // Present with another hash: refused.
        std::fs::write(dir.join("xor-bit.flat"), b"not the circuit").unwrap();
        assert_eq!(k.add_word_circuits(&dir).unwrap_err(), "word circuit pin: xor-bit");
        let _ = std::fs::remove_dir_all(&dir);
        // The pinned export in this repository (lower_word_circuits.py), when it is present.
        let real = word_circuit_dir();
        if real.join("xor-bit.flat").is_file() {
            let mut k = Kernels::default();
            assert_eq!(k.add_word_circuits(&real).unwrap(), vec!["xor-bit"]);
            assert_eq!(k.sig(b"xor-bit"), Some(Sig { in_width: 2, out_marks: vec![Mark::Never] }));
            // Twice: the name is taken.
            assert!(k.add_word_circuits(&real).is_err());
            let c = Circuits::Unpinned;
            assert_ne!(agreement_digest(&c, &["xor-bit"]), agreement_digest(&c, &[]));
        }
    }

    #[test]
    fn production_requires_a_manifest() {
        assert!(Circuits::from_environment(None, false).is_err());
        assert!(Circuits::from_environment(Some(String::new()), false).is_err());
        assert!(matches!(Circuits::from_environment(None, true), Ok(Circuits::Unpinned)));
    }
}
