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
    /// Every kernel name, in order.
    pub fn names(&self) -> impl Iterator<Item = &Vec<u8>> {
        self.entries.keys()
    }
}

/// `ReceiveFirst.varintWidth`.
fn varint_width(n: u64) -> u64 {
    if n < 128 { 1 } else if n < 16384 { 2 } else if n < 2097152 { 3 } else { 4 }
}

/// `ReceiveFirst.bodyOf` (natural subtraction saturates, as Lean's).
fn body_of(total: u64) -> u64 {
    if total.saturating_sub(2) < 128 {
        total.saturating_sub(2)
    } else if total.saturating_sub(3) < 16384 {
        total.saturating_sub(3)
    } else {
        total.saturating_sub(4)
    }
}

/// The receiver record's width in bytes, `receive-session`'s third output: `Receive.receiverBytes` in
/// TlsMpc/Node/Flows/Receive.lean (the one definition the session script slices by; proved equal to
/// the kernel's output width, `ReceiveFlowProofs.session_receiver_bits`). The test
/// `receiver_bytes_is_the_scripts` reads it from the `layout receive-session receiver` line the S14
/// vectors print from that definition (J21: this was 236, a slip in the kernels' documentation).
pub const RECEIVER_BYTES: u64 = 200;

/// Stage S14 (TlsMpc/Node/Flows/Receive.lean): the layout a receive script assumes for the kernel
/// of this manifest name (the closed forms of `Receive.*Out` and the kernels' inputs,
/// `ReceiveKernels.lean`): the input bits of one copy (`None`: not checked, the certificate's
/// signer size needs `certShape`) and the output fields' bits and marks, in order. `None` for a
/// name that is not a receive kernel or whose parameters do not parse.
pub fn receive_kernel_expected(name: &str) -> Option<(Option<u64>, Vec<(u64, Mark)>)> {
    use Mark::{Never as N, Pub as P};
    let mut words = name.split(' ');
    let stem = words.next()?;
    let a: Vec<u64> = words.map(|w| w.parse::<u64>().ok()).collect::<Option<Vec<u64>>>()?;
    let w = 255u64;
    let conversation = |cert: u64| 8 * (cert + 319);
    Some(match (stem, a.as_slice()) {
        ("receive-envelope-point", [s]) => (Some(8 * s), vec![(w, N)]),
        ("receive-unseal-static", [s]) => (Some(8 * s + 256 + w), vec![(8, N), (256, N), (w, N), (256, N)]),
        ("receive-unseal-message", [s]) => {
            let message_at = 82 + varint_width(body_of(s.saturating_sub(81)));
            let u = s.saturating_sub(message_at).saturating_sub(10);
            (Some(8 * s + 8 + 256 + w), vec![(8, N), (8 * u, N), (16, P)])
        }
        ("receive-content-shape", [u, _, _]) => (Some(8 * u + 8), vec![(32, P)]),
        ("receive-content", [u, c0, c1, hint]) => {
            let cert = c0 % 128 + 128 * c1;
            let msg = body_of(u.saturating_sub(5 + cert).saturating_sub(if *hint == 1 { 2 } else { 0 }));
            (Some(8 * u + 8), vec![(8, N), (8, N), (8 * cert, N), (8 * msg, N)])
        }
        ("receive-certificate", [_, _, _, _]) => (None, vec![(8, N), (128, N), (8, N), (512, N), (1, N), (256, N), (253, N)]),
        ("receive-certificate-verified", []) => (Some(8 + 512 + 3 * w), vec![(8, N)]),
        ("receive-prekey-shape", [n]) => (Some(8 * n + 8), vec![(168, P)]),
        ("receive-prekey-open", [n, _, _, _, _]) => (
            Some(8 * n + 8 + 8 + 256),
            vec![(8, N), (w, N), (w, N), (32, P), (32, P), (32, P), (8 * 1568, P)],
        ),
        ("receive-signal-shape", [n, _, _, _, _]) => (Some(8 * n + 8), vec![(104, P)]),
        ("receive-session", [cert, n, one, _, _, _, _, _, low, high, _, _]) => {
            let ct = if *high == 0 { *low } else { low % 128 + 128 * high };
            let dh4 = if *one > 0 { w } else { 0 };
            let input = 8 * n + 8 + 8 + 256 + 256 + 136 + 128 + 8 + 3 * w + dh4 + 256 + 6 * w + 8 * cert + 128 + 64;
            (Some(input), vec![(8, P), (conversation(*cert), N), (8 * RECEIVER_BYTES, N), (8 * (8 + ct), N)])
        }
        ("receive-text", [ct, cap]) => (Some(8 * (8 + ct)), vec![(8, P), (16, P), (8 * cap, P), (24, P)]),
        ("receive-access-key", [cert, ct, _]) => (Some(conversation(*cert) + 8 * (8 + ct)), vec![(8, P), (conversation(*cert), N)]),
        _ => return None,
    })
}

/// The receive kernels of this table whose layout is not the one the S14 scripts assume, and a
/// missing `receive-certificate-verified` (empty: the receive scripts may run; otherwise the
/// worker that would run them must not start: fails closed).
pub fn receive_kernels_check(k: &Kernels) -> Vec<String> {
    let mut bad = Vec::new();
    if k.sig(b"receive-certificate-verified").is_none() {
        bad.push("receive-certificate-verified: missing".to_string());
    }
    for name in k.names() {
        let Ok(text) = std::str::from_utf8(name) else { continue };
        if !text.starts_with("receive-") {
            continue;
        }
        let Some((input, fields)) = receive_kernel_expected(text) else {
            bad.push(format!("{text}: not a receive kernel the scripts know"));
            continue;
        };
        let sig = k.sig(name).expect("listed");
        let marks: Vec<Mark> = fields.iter().flat_map(|(bits, m)| std::iter::repeat_n(*m, *bits as usize)).collect();
        if input.is_some_and(|i| i != sig.in_width) || marks != sig.out_marks {
            bad.push(format!("{text}: signature"));
        }
    }
    bad
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

/// Stage S13 (TlsMpc/Node/Flows/Send.lean): a contact record's bytes (`service_kernels.h` CONTACT).
pub const SEND_RECORD_BYTES: u64 = 319;

/// The prefix of a seal kernel's name for this certificate size (`Send.sealName`, `bundleSealName`).
const SEND_SEAL_KERNELS: &[&str] = &["signal-seal-official", "signal-seal-built", "bundle-seal"];
const SEND_REQUEST_KERNELS: &[&str] = &["signal-request-ctr", "bundle-request-ctr"];

/// Stage S13: the manifest kernels the Lean send scripts name, with the layouts their WF theorems
/// assume (`SendProofs.SealSigs`, `requestCtrScript_wf`). The names carry shape parameters, so the
/// check is by family: `signal-widths CERT` must be present (conversation in, 21 public flag bytes
/// out); every seal kernel of this certificate size (`signal-seal-official|built CERT …`,
/// `bundle-seal CERT …`) must output a public status byte, the private conversation (certificate ‖
/// record) and a public timestamp ‖ envelope; every request sealer (`signal-request-ctr …`,
/// `bundle-request-ctr …`) public accepted ‖ header ‖ ciphertext and a private 16-byte pad; and at
/// least one seal kernel and one request sealer must be present. A worker that would run the send
/// scripts must not start unless this is empty (fails closed).
pub fn send_script_kernels_check(k: &Kernels, cert: u64) -> Vec<String> {
    let mut bad = Vec::new();
    let conv = 8 * (cert + SEND_RECORD_BYTES);
    let widths = format!("signal-widths {cert}");
    match k.sig(widths.as_bytes()) {
        None => bad.push(format!("{widths}: missing")),
        Some(s) => {
            if s.in_width != conv || s.out_marks.len() != 168 || s.out_marks.iter().any(|m| *m != Mark::Pub) {
                bad.push(format!("{widths}: signature"));
            }
        }
    }
    let (mut seals, mut requests) = (0, 0);
    for (name, kernel) in &k.entries {
        let name = String::from_utf8_lossy(name).to_string();
        let words: Vec<&str> = name.split(' ').collect();
        let family = words.first().copied().unwrap_or("");
        if SEND_SEAL_KERNELS.contains(&family) && words.get(1).and_then(|c| c.parse::<u64>().ok()) == Some(cert) {
            seals += 1;
            let m = &kernel.sig.out_marks;
            let ok = m.len() as u64 >= 8 + conv + 64
                && m[..8].iter().all(|x| *x == Mark::Pub)
                && m[8..8 + conv as usize].iter().all(|x| *x == Mark::Never)
                && m[8 + conv as usize..].iter().all(|x| *x == Mark::Pub)
                && kernel.sig.in_width >= conv + 4 * 255;
            if !ok {
                bad.push(format!("{name}: signature"));
            }
        } else if SEND_REQUEST_KERNELS.contains(&family) {
            requests += 1;
            let m = &kernel.sig.out_marks;
            let ok = m.len() > 128 + 8 + 40
                && m[..m.len() - 128].iter().all(|x| *x == Mark::Pub)
                && m[m.len() - 128..].iter().all(|x| *x == Mark::Never);
            if !ok {
                bad.push(format!("{name}: signature"));
            }
        }
    }
    if seals == 0 {
        bad.push(format!("seal kernels for certificate {cert}: missing"));
    }
    if requests == 0 {
        bad.push("request sealers: missing".into());
    }
    bad
}

/// Stage S15 (TlsMpc/Node/Flows/Refresh.lean): the fixed-name manifest kernels the refresh scripts
/// run, with the signature the scripts slice at (input bits of one copy; output segments as
/// (bits, mark), in order: `bundle-rebind` opens only its last byte, `changed`). A worker that
/// would run the refresh scripts refuses to start when one is missing or has another layout (fails
/// closed, `refresh_script_kernels_check`). The shape-parameterised ones (`bundle-fetch-ctr SIZE
/// PAYLOAD UUID KEY`, `bundle-shape CAP`, `bundle-slot FIRST LAST ONETIME`, `establish-session CERT
/// ONETIME`, `contact-seal N`) are looked up by name at `run` (a missing one refuses the batch).
pub const REFRESH_SCRIPT_KERNELS: &[(&str, u64, &[(u64, Mark)])] = &[
    ("establish-points 0", 8 * 64, &[(510, Mark::Never)]),
    ("establish-points 1", 8 * 96, &[(765, Mark::Never)]),
    ("establish-challenges", 255 * 2 + 8 * (32 + 64 + 1568 + 64), &[(1020, Mark::Never)]),
    ("establish-verified", 255 * 5 + 8 * 128, &[(8, Mark::Never)]),
    ("bundle-rebind", 8 * (319 + 1 + 1 + 32), &[(8 * 33, Mark::Never), (8, Mark::Pub)]),
    ("kem-hash kyber", 8 * 1632, &[(8 * 97, Mark::Never)]),
    ("kem-ntt", 8 * 32, &[(8 * 1536, Mark::Never)]),
    ("kem-matrix 0", 8 * 1568, &[(8 * 1537, Mark::Never)]),
    ("kem-matrix 1", 8 * 1568, &[(8 * 1537, Mark::Never)]),
    ("kem-matrix 2", 8 * 1568, &[(8 * 1537, Mark::Never)]),
    ("kem-matrix 3", 8 * 1568, &[(8 * 1537, Mark::Never)]),
    ("kem-u 0", 8 * 3104, &[(8 * 352, Mark::Never)]),
    ("kem-u 1", 8 * 3104, &[(8 * 352, Mark::Never)]),
    ("kem-u 2", 8 * 3104, &[(8 * 352, Mark::Never)]),
    ("kem-u 3", 8 * 3104, &[(8 * 352, Mark::Never)]),
    ("kem-v", 8 * 3168, &[(8 * 160, Mark::Never)]),
    ("kem-finish kyber", 8 * 1605, &[(8 * 1601, Mark::Never)]),
];

/// The S15 fixed-name kernels this kernel table lacks or has with another signature (empty: the
/// refresh scripts may run; otherwise they must not start).
pub fn refresh_script_kernels_check(k: &Kernels) -> Vec<String> {
    let mut bad = Vec::new();
    for (name, in_width, segments) in REFRESH_SCRIPT_KERNELS {
        let want: Vec<Mark> = segments.iter().flat_map(|(n, m)| std::iter::repeat(*m).take(*n as usize)).collect();
        match k.sig(name.as_bytes()) {
            None => bad.push(format!("{name}: missing")),
            Some(s) => {
                if s.in_width != *in_width || s.out_marks != want {
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
    // Stage S10 (Flows/Masks, Flows/Convert): the exported programs' pins, from the V3 re-export
    // (FIELD_PROGRAMS_V3.md: `.deps/emp-hybrid-word-v1/field_program_v3_pins.txt`, 2026-11-13; the
    // test `pins_equal_the_reexport` compares them when that file is present). A present file
    // with another hash is refused ("field program pin: …") and the worker does not start; an
    // absent file is not loaded and `check` refuses every `program` that names it.
    FieldProgramPin { name: "field-bit-check", file: "field-bit-check.v3", sha256: "aa5e5a4c7b4ee2860d2bb3f7de47143d32bbe3d204c8cb97656020ecc067ec30" },
    FieldProgramPin { name: "field-bit-xor", file: "field-bit-xor.v3", sha256: "6d0f9c19c2a82f40db6f7feed8a14bb65c4b9924db5599f75271563a26cbd7b6" },
    FieldProgramPin { name: "field-recompose", file: "field-recompose.v3", sha256: "ba3dc0f5522aa254534022b43eb590208e43eaeeaefa9ec0c6af4145073d0c02" },
    // Natively written V3 (TlsMpc/Node/Flows/ConvertBase.lean `maskSub`: v − f, public): its text is
    // Lean's `render`, so its pin is known now (tests/s10_vectors.txt `native`, checked in
    // tests/s10_pair.rs). The file is written from that text (S10_NOTES.md).
    FieldProgramPin { name: "field-mask-sub", file: "field-mask-sub.v3", sha256: FIELD_MASK_SUB_SHA256 },
    // Stage S11 (Flows/Curve.lean): every curve program runs through program.rs (no
    // field_program.h). The re-export's pins; they equal the `pin` lines of tests/s11_vectors.txt
    // (Lean's render; S11_NOTES.md), checked by hand on the export (2026-11-13).
    FieldProgramPin { name: "edwards-on-curve", file: "edwards-on-curve.v3", sha256: "2ebbbac3f5e8a22e62cc6a7ba7b3379c17754c645e26618e0b971e923cf9202d" },
    FieldProgramPin { name: "edwards-add-u", file: "edwards-add-u.v3", sha256: "ba7666b48963cc1edbbd55c4e4471f47ea21c9935b6c198abc7031d859e21b93" },
    FieldProgramPin { name: "x25519-fast", file: "x25519-fast.v3", sha256: "6abf49b0d1b48e1d5ecfdc2fa5dc560913acb0b0e47a53df628e7b3e9f5432bf" },
    FieldProgramPin { name: "edwards-prepare", file: "edwards-prepare.v3", sha256: "dd49ba3e2fc7290b229e6ec97e2a98874bb2a06965ef801debbba93ee3d5d596" },
    FieldProgramPin { name: "edwards-offset-sum", file: "edwards-offset-sum.v3", sha256: "69a1590014dfcbef34e0e7efcea43d44f7e04d937b3533df285c50f3f497a918" },
    FieldProgramPin { name: "lift-open", file: "lift-open.v3", sha256: "780c7df1394833b06cb49d3bead5d3807bddddc61db772c37a439a048025a6ff" },
    FieldProgramPin { name: "lift-point", file: "lift-point.v3", sha256: "fad82486a092a3b6087c34ea336d893e871d2924f90bd28e80b651e1cf36d3f7" },
    FieldProgramPin { name: "edwards-prepare-hinted", file: "edwards-prepare-hinted.v3", sha256: "6fc578c53400e9bd3610c91878142056ae96db8416f1d60c529f9f1db5b86680" },
    FieldProgramPin { name: "edwards-offset-sum-fast", file: "edwards-offset-sum-fast.v3", sha256: "399bd75fd9852bc31e517b0739164b88b3baae9b3e567a465c4825be5e03c1a8" },
    FieldProgramPin { name: "edwards-bit-table", file: "edwards-bit-table.v3", sha256: "a8ec7ca059a824de8e4ee26886b840d95bd8d6f02cfacfa261b15fef8d269855" },
    FieldProgramPin { name: "edwards-bit-sum", file: "edwards-bit-sum.v3", sha256: "47457a1bfe8e33c8b5458f82940d0c4a966f7182714f1659c0eb06dc9787db03" },
    FieldProgramPin { name: "edwards-affine-bit-sum", file: "edwards-affine-bit-sum.v3", sha256: "3d4c1526d2698a3ef65271b38d7910727756c59ec8e6b7a8130d8c9bee9a9c5d" },
    FieldProgramPin { name: "edwards-signature-sum", file: "edwards-signature-sum.v3", sha256: "d55883881bcf89d06f0f66f894e4cfa7aee0c19dd21c24492356ad9595d78935" },
    FieldProgramPin { name: "edwards-torsion-hinted", file: "edwards-torsion-hinted.v3", sha256: "49069034e510932c17cc47746b14bc859c033eba35b86f8c0ed007a70da755a3" },
    // Stage S14 (Flows/Receive.lean `programSignature`, `programBaseCheck`): the receive programs,
    // all outputs secret (FieldProgramsV3.find). The re-export's pins (S14's vectors carry no pin
    // lines; the stand-in pair test does not load these files).
    FieldProgramPin { name: "xeddsa-check", file: "xeddsa-check.v3", sha256: "12a3f25482eacb0c2cd5ec22f0b21b43e9640722093a388654a789d29fd8e8b2" },
    FieldProgramPin { name: "xeddsa-recover", file: "xeddsa-recover.v3", sha256: "a08a3e2f13060d58b58c43b347f6ec0271d607f792ad20c4d44fa1446d8a2522" },
    FieldProgramPin { name: "receive-torsion", file: "receive-torsion.v3", sha256: "30f5484e852fe456f7edf21fafbc6c90dfe04ddc4c31a022614359fb2e1d144f" },
];

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
        // A present file that is not the pinned program fails closed: refused, the worker does not
        // start.
        let dir = std::env::temp_dir().join(format!("node-worker-s10-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("field-bit-check.v3"), b"EMP_HYBRID_FIELD_DAG_V3\n").unwrap();
        let err = Programs::default().add_pinned(&dir, FIELD_PROGRAMS).unwrap_err();
        assert_eq!(err, "field program pin: field-bit-check");
        let _ = std::fs::remove_dir_all(&dir);
        // Every pin is a SHA-256 (the re-export's; no placeholder is left), and no name is listed twice.
        assert!(FIELD_PROGRAMS.iter().all(|p| hex64(p.sha256)), "a field program pin is not a SHA-256");
        let mut names: Vec<&str> = FIELD_PROGRAMS.iter().map(|p| p.name).collect();
        names.sort();
        names.dedup();
        assert_eq!(names.len(), FIELD_PROGRAMS.len());
    }

    #[test]
    fn script_kernel_checks_on_a_manifest() {
        // SCRIPT_KERNELS_MANIFEST=…/manifest.txt: the S12/S13/S14/S15 script-kernel checks on a
        // produced set (the layouts the Lean scripts slice by vs the real kernels' layouts files);
        // unset: nothing to check. Prints every finding, then fails if there is one.
        let Ok(path) = std::env::var("SCRIPT_KERNELS_MANIFEST") else { return };
        let m = Manifest::load(Path::new(&path)).unwrap();
        let k = Kernels::from_manifest(&m).unwrap();
        let mut found: Vec<String> = Vec::new();
        found.extend(tls_script_kernels_check(&k).into_iter().map(|e| format!("tls: {e}")));
        found.extend(receive_kernels_check(&k).into_iter().map(|e| format!("receive: {e}")));
        found.extend(refresh_script_kernels_check(&k).into_iter().map(|e| format!("refresh: {e}")));
        let certs: std::collections::BTreeSet<u64> = k
            .names()
            .filter_map(|n| std::str::from_utf8(n).ok()?.strip_prefix("signal-widths ")?.parse().ok())
            .collect();
        for cert in &certs {
            found.extend(send_script_kernels_check(&k, *cert).into_iter().map(|e| format!("send {cert}: {e}")));
        }
        eprintln!("script kernels on {path}: {} kernels, certificate sizes {certs:?}, {} findings", k.entries.len(), found.len());
        for f in &found {
            eprintln!("  {f}");
        }
        assert!(found.is_empty());
    }

    #[test]
    fn pins_equal_the_reexport() {
        // The V3 re-export's pin list (FIELD_PROGRAMS_V3.md), when this machine has it: every
        // program it exported is listed here with that pin, and every program listed here was
        // exported (field-mask-sub is written from tests/s10_vectors.txt, not by the export).
        let Ok(text) = std::fs::read_to_string(word_circuit_dir().join("field_program_v3_pins.txt")) else { return };
        let exported: Vec<(&str, &str)> = text.lines().filter_map(|l| l.split_once(' ')).collect();
        for (name, sha) in &exported {
            let p = FIELD_PROGRAMS.iter().find(|p| p.name == *name).unwrap_or_else(|| panic!("{name} not in FIELD_PROGRAMS"));
            assert_eq!(p.sha256, *sha, "{name}");
        }
        for p in FIELD_PROGRAMS.iter().filter(|p| p.name != "field-mask-sub") {
            assert!(exported.iter().any(|(n, _)| *n == p.name), "{} not exported", p.name);
        }
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
    fn s13_send_kernels_fail_closed() {
        let cert = 8u64;
        let conv = 8 * (cert + SEND_RECORD_BYTES);
        let put = |k: &mut Kernels, name: &str, in_width: u64, out_marks: Vec<Mark>| {
            k.insert(name.as_bytes(), Kernel { flat: PathBuf::new(), sha256: String::new(), sig: Sig { in_width, out_marks } });
        };
        // Nothing loaded: the widths kernel, the seal kernels and the request sealers are missing.
        assert_eq!(send_script_kernels_check(&Kernels::default(), cert).len(), 3);
        // The layouts the scripts assume: accepted.
        let mut k = Kernels::default();
        put(&mut k, "signal-widths 8", conv, vec![Mark::Pub; 168]);
        let env = 261u64;
        let seal: Vec<Mark> = [vec![Mark::Pub; 8], vec![Mark::Never; conv as usize], vec![Mark::Pub; (64 + 8 * env) as usize]].concat();
        put(&mut k, "signal-seal-built 8 1 1 1 1 1", conv + 8 * 90 + 1020, seal.clone());
        let req: Vec<Mark> = [vec![Mark::Pub; 8 * 230], vec![Mark::Never; 128]].concat();
        put(&mut k, "signal-request-ctr 8 223 40 80 120 130", 8 * (68 + 327 + 223 + 4), req.clone());
        assert!(send_script_kernels_check(&k, cert).is_empty(), "{:?}", send_script_kernels_check(&k, cert));
        // A seal kernel whose conversation output is public is refused.
        put(&mut k, "signal-seal-official 8 1 1 1 1 1", conv + 8 * 89 + 1020, vec![Mark::Pub; seal.len()]);
        assert_eq!(send_script_kernels_check(&k, cert), vec!["signal-seal-official 8 1 1 1 1 1: signature".to_string()]);
        // A request sealer whose pad is public is refused.
        let mut k2 = Kernels::default();
        put(&mut k2, "signal-widths 8", conv, vec![Mark::Pub; 168]);
        put(&mut k2, "signal-seal-built 8 1 1 1 1 1", conv + 8 * 90 + 1020, seal);
        put(&mut k2, "bundle-request-ctr 300 8 20 60 100 110", 8 * (68 + 319 + 300 + 4), vec![Mark::Pub; req.len()]);
        assert_eq!(send_script_kernels_check(&k2, cert), vec!["bundle-request-ctr 300 8 20 60 100 110: signature".to_string()]);
        // Another certificate size: its widths kernel is missing.
        assert!(send_script_kernels_check(&k, 9).iter().any(|e| e == "signal-widths 9: missing"));
    }

    #[test]
    fn s14_receive_kernels_fail_closed() {
        // Nothing loaded: the fixed-name kernel is missing.
        assert_eq!(receive_kernels_check(&Kernels::default()), vec!["receive-certificate-verified: missing".to_string()]);
        let put = |k: &mut Kernels, name: &str| {
            let (input, fields) = receive_kernel_expected(name).unwrap();
            let out_marks = fields.iter().flat_map(|(b, m)| std::iter::repeat_n(*m, *b as usize)).collect();
            let sig = Sig { in_width: input.unwrap_or(7), out_marks };
            k.insert(name.as_bytes(), Kernel { flat: PathBuf::new(), sha256: String::new(), sig });
        };
        let mut k = Kernels::default();
        for name in [
            "receive-certificate-verified",
            "receive-envelope-point 400",
            "receive-unseal-static 400",
            "receive-unseal-message 400",
            "receive-content-shape 306 131 2",
            "receive-content 306 131 2 0",
            "receive-certificate 131 2 0 0",
            "receive-prekey-shape 1800",
            "receive-prekey-open 1800 0 2 1 1",
            "receive-signal-shape 1800 0 2 1 1",
            "receive-session 260 1800 0 2 1 1 1 1 48 0 0 0",
            "receive-text 48 42",
            "receive-access-key 260 48 30",
        ] {
            put(&mut k, name);
        }
        assert!(receive_kernels_check(&k).is_empty(), "{:?}", receive_kernels_check(&k));
        // The session's status kept private instead of opened: refused.
        let mut sig = k.sig(b"receive-session 260 1800 0 2 1 1 1 1 48 0 0 0").unwrap();
        sig.out_marks[0] = Mark::Never;
        k.insert(b"receive-session 260 1800 0 2 1 1 1 1 48 0 0 0", Kernel { flat: PathBuf::new(), sha256: String::new(), sig });
        assert_eq!(receive_kernels_check(&k), vec!["receive-session 260 1800 0 2 1 1 1 1 48 0 0 0: signature".to_string()]);
        // A receive kernel the scripts do not know: refused.
        k.insert(b"receive-other 1", Kernel { flat: PathBuf::new(), sha256: String::new(), sig: Sig { in_width: 8, out_marks: vec![] } });
        assert_eq!(receive_kernels_check(&k).len(), 2);
        // The receive programs are pinned (the re-export's SHA-256s; `pins_equal_the_reexport`).
        for n in ["xeddsa-check", "xeddsa-recover", "receive-torsion"] {
            assert!(hex64(FIELD_PROGRAMS.iter().find(|p| p.name == n).unwrap().sha256), "{n}");
        }
    }

    #[test]
    fn receiver_bytes_is_the_scripts() {
        // J21: the session's receiver width is the Lean script's `Receive.receiverBytes`, printed by
        // tests/lean/S14Vectors.lean into tests/s14_vectors.txt.
        let text = include_str!("../tests/s14_vectors.txt");
        let line = text.lines().find(|l| l.starts_with("layout receive-session receiver ")).expect("layout line");
        assert_eq!(line.rsplit(' ').next().unwrap().parse::<u64>().unwrap(), RECEIVER_BYTES);
        // A session kernel with the old 236-byte receiver is refused.
        let name = "receive-session 260 1800 0 2 1 1 1 1 48 0 0 0";
        let (input, mut fields) = receive_kernel_expected(name).unwrap();
        fields[2].0 = 8 * 236;
        let out_marks = fields.iter().flat_map(|(b, m)| std::iter::repeat_n(*m, *b as usize)).collect();
        let mut k = Kernels::default();
        k.insert(b"receive-certificate-verified", Kernel { flat: PathBuf::new(), sha256: String::new(),
            sig: Sig { in_width: 8 + 512 + 3 * 255, out_marks: vec![Mark::Never; 8] } });
        k.insert(name.as_bytes(), Kernel { flat: PathBuf::new(), sha256: String::new(), sig: Sig { in_width: input.unwrap(), out_marks } });
        assert_eq!(receive_kernels_check(&k), vec![format!("{name}: signature")]);
    }

    #[test]
    fn s15_refresh_kernels_fail_closed() {
        let empty = Kernels::default();
        assert_eq!(refresh_script_kernels_check(&empty).len(), REFRESH_SCRIPT_KERNELS.len());
        let mut k = Kernels::default();
        for (name, in_width, segments) in REFRESH_SCRIPT_KERNELS {
            let out_marks: Vec<Mark> = segments.iter().flat_map(|(n, m)| std::iter::repeat(*m).take(*n as usize)).collect();
            let sig = Sig { in_width: *in_width, out_marks };
            k.insert(name.as_bytes(), Kernel { flat: PathBuf::new(), sha256: String::new(), sig });
        }
        assert!(refresh_script_kernels_check(&k).is_empty());
        // A rebind whose private verified/uuid/accessKey would be openable is refused.
        let sig = Sig { in_width: 8 * 353, out_marks: vec![Mark::Pub; 8 * 34] };
        k.insert(b"bundle-rebind", Kernel { flat: PathBuf::new(), sha256: String::new(), sig });
        assert_eq!(refresh_script_kernels_check(&k), vec!["bundle-rebind: signature".to_string()]);
        // A KEM stage with a public output (the secret would be openable) is refused.
        let sig = Sig { in_width: 8 * 1605, out_marks: vec![Mark::Pub; 8 * 1601] };
        k.insert(b"kem-finish kyber", Kernel { flat: PathBuf::new(), sha256: String::new(), sig });
        assert_eq!(refresh_script_kernels_check(&k).len(), 2);
    }

    #[test]
    fn production_requires_a_manifest() {
        assert!(Circuits::from_environment(None, false).is_err());
        assert!(Circuits::from_environment(Some(String::new()), false).is_err());
        assert!(matches!(Circuits::from_environment(None, true), Ok(Circuits::Unpinned)));
    }
}
