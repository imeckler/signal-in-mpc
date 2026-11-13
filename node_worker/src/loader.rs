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
use crate::handles::{Mark, ProgSig, Sig};
use crate::program::{Program, parse};
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

/// Stage S12 (TlsMpc/Node/Flows/{Ghash,Tls}.lean): the manifest kernels the Lean TLS scripts run
/// under a fixed name, with the signature each script's WF theorem assumes (input bits of one
/// copy; output bits and their one mark). They are ordinary manifest kernels (pinned by the
/// manifest, as the legacy library's `KernelCache` loads them: no re-export is needed); this list
/// only lets a worker that would run the script backend refuse to start when one is missing or
/// has another layout (fails closed, `tls_script_kernels_check`). The shape-parameterised ones
/// (`tls-seal-ctr KIND N PAD`, `tls-seal-class CAP`, `tls-open-typed CAP`, `tls-frame CAP`,
/// `tls-reveal-masked CAP`, `tls-open-handshake N`, `tls-finish N`) are looked up by name at
/// `run` like every manifest kernel (a missing one refuses the batch).
pub const TLS_SCRIPT_KERNELS: &[(&str, u64, u64, Mark)] = &[
    // GHASH key-power shares: the masked value is opened to B only (layout code 3).
    ("gcm-key-share", 8 * 76, 128, Mark::ToB),
    ("gcm-multiply", 8 * 80, 128, Mark::ToB),
    // The tag is public; the tag check's acceptance byte is private.
    ("gcm-tag", 8 * 48, 128, Mark::Pub),
    ("gcm-check", 8 * 116, 8, Mark::Never),
    ("tls-parser-initial", 8, 88, Mark::Never),
    ("tls-update", 8 * 60, 480, Mark::Never),
    ("tls-verify-finished", 8 * 128, 8, Mark::Pub),
];

/// The S12 fixed-name kernels this kernel table lacks or has with another signature (empty: the
/// script backend may run; otherwise it must not start).
pub fn tls_script_kernels_check(k: &Kernels) -> Vec<String> {
    let mut bad = Vec::new();
    for (name, in_width, out_width, mark) in TLS_SCRIPT_KERNELS {
        match k.sig(name.as_bytes()) {
            None => bad.push(format!("{name}: missing")),
            Some(s) => {
                if s.in_width != *in_width || s.out_marks.len() as u64 != *out_width || s.out_marks.iter().any(|m| m != mark) {
                    bad.push(format!("{name}: signature"));
                }
            }
        }
    }
    bad
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
///
/// Stage S10 (TlsMpc/Node/Flows/ConvertBase.lean `WordLoaded`, the same names and marks): the
/// conversion circuits of `TlsMpc/WordMask.lean` and `TlsMpc/X25519SwapBits.lean`, with the pins
/// `word_circuit_pins.h` already carries (lower_word_circuits.py). A pinned file may be registered
/// under two names with different output marks: `modadd` (field to word: the result stays private)
/// and `modadd-open` (the bucket check: opened); `xor-bit` and `xor-bit-open` (bits to field: the
/// masked bit is opened). `finalize-mask` / `finalize-bits`: 255 private bits, then the public flag.
/// `into-field-open`: the masked word of word to field (opened). `swap-bits`: 252 private bits.
pub const WORD_CIRCUITS: &[WordCircuit] = &[
    WordCircuit {
        name: "xor-bit",
        file: "xor-bit.flat",
        sha256: WORD_XOR_BIT_SHA256,
        in_width: 2,
        out_marks: &[Mark::Never],
    },
    WordCircuit { name: "xor-bit-open", file: "xor-bit.flat", sha256: WORD_XOR_BIT_SHA256, in_width: 2, out_marks: &[Mark::Pub] },
    WordCircuit { name: "modadd", file: "modadd.flat", sha256: WORD_MODADD_SHA256, in_width: 510, out_marks: &NEVER_255 },
    WordCircuit { name: "modadd-open", file: "modadd.flat", sha256: WORD_MODADD_SHA256, in_width: 510, out_marks: &PUB_255 },
    WordCircuit {
        name: "finalize-mask",
        file: "finalize-mask.flat",
        sha256: "a75d51c2a8bb91340ce67e862c40004f5ed82c54d4bf2d382184a17b1085f78b",
        in_width: 510,
        out_marks: &FINAL_MARKS,
    },
    WordCircuit {
        name: "finalize-bits",
        file: "finalize-bits.flat",
        sha256: "acf15435c59a090ab66ae2808db5ddc8ded70d25364cdd65e54aa5b24cbb2060",
        in_width: 510,
        out_marks: &FINAL_MARKS,
    },
    WordCircuit {
        name: "into-field-open",
        file: "into-field.flat",
        sha256: "d4888fa12489dadd4aa4937d613c78b36736fad61e30c6f2e21c02d283f22c70",
        in_width: 510,
        out_marks: &PUB_255,
    },
    WordCircuit {
        name: "swap-bits",
        file: "swap-bits.flat",
        sha256: "6c981ca7f9e63f434d28338d89e1e5768dbc4e9578a05d1956ab6e152fbd60a7",
        in_width: 256,
        out_marks: &NEVER_252,
    },
];

const WORD_XOR_BIT_SHA256: &str = "6495137f2dc968d4553b3560a5e09d4a1cdc182503460dbb0773783f35feadac";
const WORD_MODADD_SHA256: &str = "20ab904cf9a10d7cfd0ee45af4e77eb78fa3551ff1e0f657f9121e7ce6baea04";
const NEVER_255: [Mark; 255] = [Mark::Never; 255];
const PUB_255: [Mark; 255] = [Mark::Pub; 255];
const NEVER_252: [Mark; 252] = [Mark::Never; 252];
const FINAL_MARKS: [Mark; 256] = final_marks();
const fn final_marks() -> [Mark; 256] {
    let mut m = [Mark::Never; 256];
    m[255] = Mark::Pub;
    m
}

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
/// alone when no word circuit and no field program is runnable, otherwise SHA-256 of it, each
/// added word circuit's name and pin, and each added V3 field program's name and pin, so two
/// workers that could run different circuit or program sets stop before any request.
pub fn agreement_digest(circuits: &Circuits, words: &[&str], programs: &[&str]) -> [u8; 32] {
    if words.is_empty() && programs.is_empty() {
        return circuits.digest();
    }
    let mut h = Sha256::new();
    h.update(circuits.digest());
    for name in words {
        let w = WORD_CIRCUITS.iter().find(|w| w.name == *name).expect("a listed word circuit");
        h.update(format!("\nword {} {}", w.name, w.sha256).as_bytes());
    }
    for name in programs {
        let p = FIELD_PROGRAMS.iter().find(|p| p.name == *name).expect("a listed field program");
        h.update(format!("\nprogram {} {}", p.name, p.sha256).as_bytes());
    }
    h.finalize().into()
}

/// A V3 field program the `program` instruction may name (TlsMpc/FieldDagV3.lean, program.rs):
/// its file in the word-circuit directory (written by the V3 export of `EmitWordMask`,
/// FIELD_PROGRAMS_V3.md) and the file's pin. The file is parsed by program.rs, which accepts only
/// a valid program's canonical text (Lean `parse`), so the pin names one program.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FieldProgramPin {
    /// The name a batch's `program` uses.
    pub name: &'static str,
    pub file: &'static str,
    pub sha256: &'static str,
}

/// The V3 field programs `program` may name. `field-quotient`: `x / z` with a mask and the
/// public zero flag (Lean `FieldDagV3.quotient`; its text is fixed by Lean's printer, so its pin
/// is known before the export; tests/engine_vectors.txt carries the text). The compiled
/// programs' pins are added from the re-export's report (FIELD_PROGRAMS_V3.md).
pub const FIELD_PROGRAMS: &[FieldProgramPin] = &[
    FieldProgramPin { name: "field-quotient", file: "field-quotient.v3", sha256: FIELD_QUOTIENT_SHA256 },
    // Stage S10 (Flows/Masks, Flows/Convert): the exported programs' pins come from the V3
    // re-export (FIELD_PROGRAMS_V3.md, `field_program_v3_pins.rs.txt`). Until then these are
    // PLACEHOLDERS that FAIL CLOSED: no SHA-256 equals them, so a present file is refused
    // ("field program pin: …") and the worker does not start; an absent file is not loaded and
    // `check` refuses every `program` that names it.
    FieldProgramPin { name: "field-bit-check", file: "field-bit-check.v3", sha256: PIN_FROM_REEXPORT },
    FieldProgramPin { name: "field-bit-xor", file: "field-bit-xor.v3", sha256: PIN_FROM_REEXPORT },
    FieldProgramPin { name: "field-recompose", file: "field-recompose.v3", sha256: PIN_FROM_REEXPORT },
    // Natively written V3 (TlsMpc/Node/Flows/ConvertBase.lean `maskSub`: v − f, public): its text is
    // Lean's `render`, so its pin is known now (tests/s10_vectors.txt `native`, checked in
    // tests/s10_pair.rs). The file is written from that text (S10_NOTES.md).
    FieldProgramPin { name: "field-mask-sub", file: "field-mask-sub.v3", sha256: FIELD_MASK_SUB_SHA256 },
];

/// The placeholder pin of the S10 programs the re-export has not produced yet (not hex: never a
/// SHA-256, so it fails closed).
pub const PIN_FROM_REEXPORT: &str = "PLACEHOLDER-S10-pin-from-the-V3-re-export";

/// SHA-256 of `render FieldDagV3.quotient` (checked against the Lean text in
/// tests/program_vectors.rs).
pub const FIELD_QUOTIENT_SHA256: &str = "ec4abf2bfd564dae04801e00de2d6ca21503321c1af86909fb2871007f8f1e34";

/// SHA-256 of `render Conv.maskSub` (`field-mask-sub`; checked against the Lean text in
/// tests/s10_pair.rs).
pub const FIELD_MASK_SUB_SHA256: &str = "1dd3b23751bf286d034dad86bf90bd9ab46ec0e35adb90eb3da57b4b6c6ff4bf";

/// The V3 field programs of `program` (interp.rs), by name, parsed.
#[derive(Debug, Clone, Default)]
pub struct Programs {
    entries: BTreeMap<Vec<u8>, Program>,
}

impl Programs {
    pub fn insert(&mut self, name: &[u8], program: Program) {
        self.entries.insert(name.to_vec(), program);
    }
    pub fn get(&self, name: &[u8]) -> Option<&Program> {
        self.entries.get(name)
    }
    /// Lean `Ctx.progs` at session start (Lean `Env.progs`).
    pub fn sigs(&self) -> BTreeMap<Vec<u8>, ProgSig> {
        self.entries.iter().map(|(n, p)| (n.clone(), p.sig())).collect()
    }
    /// Adds every pinned program of `pins` whose file is in `dir`, after checking the file
    /// against its pin and parsing it (program.rs `parse`, Lean `parse`). A file present with
    /// another hash, or that does not parse, is an error; an absent file is not added (then
    /// `check` refuses a `program` naming it). Returns the names added, which the start agreement
    /// covers ([`agreement_digest`]).
    pub fn add_pinned(&mut self, dir: &Path, pins: &[FieldProgramPin]) -> Result<Vec<&'static str>, String> {
        let mut added = Vec::new();
        for pin in pins {
            let path = dir.join(pin.file);
            let Ok(bytes) = std::fs::read(&path) else { continue };
            if hex(&Sha256::digest(&bytes)) != pin.sha256 {
                return Err(format!("field program pin: {}", pin.name));
            }
            let program = parse(&bytes).map_err(|e| format!("{e}: {}", pin.name))?;
            if self.get(pin.name.as_bytes()).is_some() {
                return Err(format!("field program listed twice: {}", pin.name));
            }
            self.insert(pin.name.as_bytes(), program);
            added.push(pin.name);
        }
        Ok(added)
    }
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
            let added = k.add_word_circuits(&real).unwrap();
            assert!(added.contains(&"xor-bit") && added.contains(&"xor-bit-open"));
            assert_eq!(k.sig(b"xor-bit"), Some(Sig { in_width: 2, out_marks: vec![Mark::Never] }));
            assert_eq!(k.sig(b"xor-bit-open"), Some(Sig { in_width: 2, out_marks: vec![Mark::Pub] }));
            // Twice: the name is taken.
            assert!(k.add_word_circuits(&real).is_err());
            let c = Circuits::Unpinned;
            assert_ne!(agreement_digest(&c, &["xor-bit"], &[]), agreement_digest(&c, &[], &[]));
        }
    }

    #[test]
    fn field_programs_are_pinned_and_parsed() {
        let dir = std::env::temp_dir().join(format!("node-worker-programs-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let text = format!(
            "EMP_HYBRID_FIELD_DAG_V3\n2 1 4 2\n{}\nI 0\nI 1\nZ 0 1 0\nF 2\nO 2 0\nO 3 1\n",
            std::str::from_utf8(crate::program::MODULUS_DECIMAL).unwrap()
        );
        let sha = hex(&Sha256::digest(text.as_bytes()));
        let leaked = |s: String| -> &'static str { Box::leak(s.into_boxed_str()) };
        let pins = [FieldProgramPin { name: "q", file: "q.v3", sha256: leaked(sha) }];
        let mut p = Programs::default();
        // Absent: not added.
        assert_eq!(p.add_pinned(&dir, &pins).unwrap(), Vec::<&str>::new());
        // Present and pinned: parsed, and its signature is check's.
        std::fs::write(dir.join("q.v3"), &text).unwrap();
        assert_eq!(p.add_pinned(&dir, &pins).unwrap(), vec!["q"]);
        assert_eq!(p.sigs()[b"q".as_slice()], ProgSig { inputs: 2, masks: 1, out_marks: vec![Mark::Never, Mark::Pub] });
        // Twice: refused.
        assert!(p.add_pinned(&dir, &pins).is_err());
        // Another hash: refused.
        std::fs::write(dir.join("q.v3"), format!("{text} ")).unwrap();
        assert_eq!(Programs::default().add_pinned(&dir, &pins).unwrap_err(), "field program pin: q");
        let _ = std::fs::remove_dir_all(&dir);
        let c = Circuits::Unpinned;
        assert_ne!(agreement_digest(&c, &[], &["field-quotient"]), agreement_digest(&c, &[], &[]));
    }

    #[test]
    fn s10_word_circuits_and_placeholders() {
        // The S10 word circuits: the shapes and marks of ConvertBase.lean `WordLoaded`.
        let get = |n: &str| WORD_CIRCUITS.iter().find(|w| w.name == n).unwrap();
        assert_eq!((get("modadd").in_width, get("modadd").out_marks.len()), (510, 255));
        assert!(get("modadd").out_marks.iter().all(|m| *m == Mark::Never));
        assert!(get("modadd-open").out_marks.iter().all(|m| *m == Mark::Pub));
        assert_eq!(get("modadd").sha256, get("modadd-open").sha256);
        for n in ["finalize-mask", "finalize-bits"] {
            let m = get(n).out_marks;
            assert_eq!(m.len(), 256);
            assert!(m[..255].iter().all(|x| *x == Mark::Never) && m[255] == Mark::Pub, "{n}");
        }
        assert!(get("into-field-open").out_marks.iter().all(|m| *m == Mark::Pub));
        assert_eq!((get("swap-bits").in_width, get("swap-bits").out_marks.len()), (256, 252));
        // The names are distinct.
        let mut names: Vec<&str> = WORD_CIRCUITS.iter().map(|w| w.name).collect();
        names.sort();
        names.dedup();
        assert_eq!(names.len(), WORD_CIRCUITS.len());
        // A placeholder pin fails closed: a present file is refused, the worker does not start.
        let dir = std::env::temp_dir().join(format!("node-worker-s10-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("field-bit-check.v3"), b"EMP_HYBRID_FIELD_DAG_V3\n").unwrap();
        let err = Programs::default().add_pinned(&dir, FIELD_PROGRAMS).unwrap_err();
        assert_eq!(err, "field program pin: field-bit-check");
        let _ = std::fs::remove_dir_all(&dir);
        assert!(!PIN_FROM_REEXPORT.chars().all(|c| c.is_ascii_hexdigit()));
    }

    #[test]
    fn s12_tls_kernels_fail_closed() {
        // Nothing loaded: every S12 kernel is reported missing.
        let empty = Kernels::default();
        assert_eq!(tls_script_kernels_check(&empty).len(), TLS_SCRIPT_KERNELS.len());
        // The signatures the scripts' WF theorems assume: accepted.
        let mut k = Kernels::default();
        for (name, in_width, out_width, mark) in TLS_SCRIPT_KERNELS {
            let sig = Sig { in_width: *in_width, out_marks: vec![*mark; *out_width as usize] };
            k.insert(name.as_bytes(), Kernel { flat: PathBuf::new(), sha256: String::new(), sig });
        }
        assert!(tls_script_kernels_check(&k).is_empty());
        // A key share opened to both parties instead of to B only is refused.
        let sig = Sig { in_width: 8 * 76, out_marks: vec![Mark::Pub; 128] };
        k.insert(b"gcm-key-share", Kernel { flat: PathBuf::new(), sha256: String::new(), sig });
        assert_eq!(tls_script_kernels_check(&k), vec!["gcm-key-share: signature".to_string()]);
    }

    #[test]
    fn production_requires_a_manifest() {
        assert!(Circuits::from_environment(None, false).is_err());
        assert!(Circuits::from_environment(Some(String::new()), false).is_err());
        assert!(matches!(Circuits::from_environment(None, true), Ok(Circuits::Unpinned)));
    }
}
