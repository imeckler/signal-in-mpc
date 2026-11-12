//! The Lean-generated vectors (tests/engine_vectors.txt, written by tests/lean/EngineVectors.lean
//! through .deps/lowering-scratch/s9r_vectors.py), parsed for the tests.
#![allow(dead_code)]
pub mod field;

use node_worker::handles::{Mark, Sig};
use node_worker::loader::Programs;

/// The loaded V3 programs (`prog NAME_HEX TEXT_HEX …`), parsed by program.rs.
pub fn programs(text: &str) -> Programs {
    let mut p = Programs::default();
    for l in text.lines().filter_map(|l| l.strip_prefix("prog ")) {
        let f: Vec<&str> = l.split(' ').collect();
        let program = node_worker::program::parse(&unhex(f[1])).expect("Lean's V3 text parses");
        p.insert(&unhex(f[0]), program);
    }
    p
}

/// Field elements from Lean's `Enc.felts` hex (a u64 count, then 32 bytes each).
pub fn felts(hexed: &str) -> Vec<[u8; 32]> {
    let b = unhex(hexed);
    let n = u64::from_le_bytes(b[..8].try_into().unwrap()) as usize;
    assert_eq!(b.len(), 8 + 32 * n, "felts");
    (0..n).map(|i| b[8 + 32 * i..8 + 32 * (i + 1)].try_into().unwrap()).collect()
}

pub fn unhex(s: &str) -> Vec<u8> {
    assert!(s.len() % 2 == 0, "odd hex");
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).expect("hex")).collect()
}

pub fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

pub fn text() -> String {
    std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/engine_vectors.txt")).expect("tests/engine_vectors.txt")
}

fn mark(c: char) -> Mark {
    match c {
        '0' => Mark::Never,
        '1' => Mark::Pub,
        '2' => Mark::ToA,
        '3' => Mark::ToB,
        '4' => Mark::Revealable,
        _ => panic!("mark {c}"),
    }
}

/// The signatures the vectors were checked with (`sig NAME_HEX IN_WIDTH MARKS`).
pub fn sigs(text: &str) -> Vec<(Vec<u8>, Sig)> {
    text.lines()
        .filter_map(|l| l.strip_prefix("sig "))
        .map(|l| {
            let f: Vec<&str> = l.split(' ').collect();
            (unhex(f[0]), Sig { in_width: f[1].parse().unwrap(), out_marks: f.get(2).map_or(vec![], |m| m.chars().map(mark).collect()) })
        })
        .collect()
}

/// One round of a two-party flow: each party's batch and the reply it must get.
#[derive(Debug, Clone, Default)]
pub struct Round {
    pub batch: [Vec<u8>; 2],
    pub reply: [Vec<u8>; 2],
}

#[derive(Debug, Clone)]
pub struct Flow {
    pub name: String,
    pub rounds: Vec<Round>,
    pub results: Vec<String>,
}

/// The `flow` blocks.
pub fn flows(text: &str) -> Vec<Flow> {
    let mut out: Vec<Flow> = Vec::new();
    let mut party = 0usize;
    for line in text.lines() {
        let (key, rest) = line.split_once(' ').unwrap_or((line, ""));
        match key {
            "flow" => out.push(Flow { name: rest.to_string(), rounds: vec![], results: vec![] }),
            "round" => out.last_mut().unwrap().rounds.push(Round::default()),
            "party" => party = if rest == "a" { 0 } else { 1 },
            "batch" if !out.is_empty() && !out.last().unwrap().rounds.is_empty() => {
                out.last_mut().unwrap().rounds.last_mut().unwrap().batch[party] = unhex(rest);
            }
            "reply" => out.last_mut().unwrap().rounds.last_mut().unwrap().reply[party] = unhex(rest),
            "result" => out.last_mut().unwrap().results.push(rest.to_string()),
            "case" => {
                // cases come before flows; nothing to collect
            }
            _ => {}
        }
    }
    out
}

/// The `case` blocks: name and batches (in order).
pub fn cases(text: &str) -> Vec<(String, Vec<Vec<u8>>)> {
    let mut out: Vec<(String, Vec<Vec<u8>>)> = Vec::new();
    let mut inside = false;
    for line in text.lines() {
        let (key, rest) = line.split_once(' ').unwrap_or((line, ""));
        match key {
            "case" => {
                out.push((rest.to_string(), vec![]));
                inside = true;
            }
            "end" => inside = false,
            "batch" if inside => out.last_mut().unwrap().1.push(unhex(rest)),
            _ => {}
        }
    }
    out
}
