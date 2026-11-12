//! program.rs against Lean: every V3 vector of tests/engine_vectors.txt (computed by
//! TlsMpc/FieldDagV3.lean and the model's `runProgram`, through tests/lean/EngineVectors.lean).
//! - `prog`: Lean's text of each loaded program parses here, with Lean's signature and number of
//!   openings; the pinned `field-quotient` text has the pin loader.rs carries.
//! - `v3parse`: program.rs accepts exactly the texts Lean's `parse` accepts (and an accepted text
//!   is the rendered text, Lean `render_parse`).
//! - `v3eval`: program.rs's `evaluate` over a stand-in field engine (clear arithmetic mod p, one
//!   party) returns Lean's outputs and openings, or aborts where Lean's run aborts; every engine
//!   value it made is freed except the outputs, which are values of their own.
mod common;

use common::field::{Fe, add, bytes_of, fe_of, inv, mul, sub};
use common::{felts, hex, unhex};
use node_worker::engines::{Counters, Engines};
use node_worker::loader::{FIELD_PROGRAMS, FIELD_QUOTIENT_SHA256};
use node_worker::program::{evaluate, parse};
use sha2::{Digest, Sha256};
use std::collections::HashMap;

/// A one-party field engine in the clear: handles to values, and a log of the calls.
#[derive(Default)]
struct Clear {
    next: u64,
    fields: HashMap<u64, Fe>,
    opened: usize,
}

impl Clear {
    fn put(&mut self, v: Fe) -> u64 {
        self.next += 1;
        self.fields.insert(self.next, v);
        self.next
    }
    fn get(&self, h: u64) -> Result<Fe, String> {
        self.fields.get(&h).copied().ok_or_else(|| format!("unknown handle {h}"))
    }
}

impl Engines for Clear {
    fn counters(&mut self) -> Counters {
        Counters::default()
    }
    fn legacy(&mut self, _: u8, _: u64, _: &[u8]) -> Result<Vec<u8>, String> {
        Err("none".into())
    }
    fn select(&mut self, _: u8) -> Result<(), String> {
        Ok(())
    }
    fn reset(&mut self) -> Result<(), String> {
        Ok(())
    }
    fn abort(&mut self) {}
    fn profile_report(&mut self, _: &str) {}
    fn field_constant(&mut self, value: u64) -> Result<u64, String> {
        Ok(self.put([value, 0, 0, 0]))
    }
    fn field_public(&mut self, value: &[u8; 32]) -> Result<u64, String> {
        Ok(self.put(fe_of(value)))
    }
    fn field_add(&mut self, a: u64, b: u64) -> Result<u64, String> {
        let v = add(&self.get(a)?, &self.get(b)?);
        Ok(self.put(v))
    }
    fn field_sub(&mut self, a: u64, b: u64) -> Result<u64, String> {
        let v = sub(&self.get(a)?, &self.get(b)?);
        Ok(self.put(v))
    }
    fn field_scale(&mut self, a: u64, constant: u64) -> Result<u64, String> {
        let v = mul(&self.get(a)?, &[constant, 0, 0, 0]);
        Ok(self.put(v))
    }
    fn field_divide_public(&mut self, a: u64, c: &[u8; 32]) -> Result<u64, String> {
        let v = mul(&self.get(a)?, &inv(&fe_of(c)));
        Ok(self.put(v))
    }
    fn field_mul(&mut self, a: &[u64], b: &[u64]) -> Result<Vec<u64>, String> {
        let mut out = vec![];
        for (&x, &y) in a.iter().zip(b) {
            let v = mul(&self.get(x)?, &self.get(y)?);
            out.push(self.put(v));
        }
        Ok(out)
    }
    fn field_checked_open(&mut self, hs: &[u64]) -> Result<Vec<[u8; 32]>, String> {
        self.opened += hs.len();
        hs.iter().map(|&h| self.get(h).map(|v| bytes_of(&v))).collect()
    }
    fn field_free(&mut self, h: u64) -> Result<(), String> {
        self.fields.remove(&h).map(|_| ()).ok_or_else(|| format!("free of unknown handle {h}"))
    }
}

#[test]
fn programs_parse_with_leans_signatures() {
    let text = common::text();
    let mut seen = 0;
    for l in text.lines().filter_map(|l| l.strip_prefix("prog ")) {
        let f: Vec<&str> = l.split(' ').collect();
        let name = String::from_utf8(unhex(f[0])).unwrap();
        let body = unhex(f[1]);
        let p = parse(&body).unwrap_or_else(|e| panic!("{name}: {e}"));
        let sig = p.sig();
        assert_eq!((sig.inputs.to_string(), sig.masks.to_string()), (f[2].to_string(), f[3].to_string()), "{name}");
        assert_eq!(sig.out_marks.iter().map(|m| m.code()).collect::<String>(), f[4], "{name}: output marks");
        assert_eq!(p.openings().to_string(), f[5], "{name}: openings");
        if name == "field-quotient" {
            assert_eq!(hex(&Sha256::digest(&body)), FIELD_QUOTIENT_SHA256, "the pin of Lean's quotient text");
            assert!(FIELD_PROGRAMS.iter().any(|p| p.name == "field-quotient" && p.sha256 == FIELD_QUOTIENT_SHA256));
        }
        seen += 1;
    }
    assert_eq!(seen, 2);
}

#[test]
fn parser_agrees_with_lean() {
    let text = common::text();
    let (mut ok, mut none) = (0, 0);
    for l in text.lines().filter_map(|l| l.strip_prefix("v3parse ")) {
        let f: Vec<&str> = l.split(' ').collect();
        let input = unhex(f[0]);
        let got = parse(&input);
        match f[1] {
            "ok" => {
                ok += 1;
                assert!(got.is_ok(), "Lean accepts {:?}: {:?}", String::from_utf8_lossy(&input), got);
                assert_eq!(f[2], f[0], "Lean: an accepted text is its program's rendering");
            }
            "none" => {
                none += 1;
                assert!(got.is_err(), "Lean refuses {:?}", String::from_utf8_lossy(&input));
            }
            other => panic!("{other}"),
        }
    }
    assert!(ok >= 2 && none >= 20, "{ok} {none}");
}

#[test]
fn evaluation_agrees_with_lean() {
    let text = common::text();
    let programs = common::programs(&text);
    let (mut runs, mut aborts) = (0, 0);
    for l in text.lines().filter_map(|l| l.strip_prefix("v3eval ")) {
        let f: Vec<&str> = l.split(' ').collect();
        let name = unhex(f[0]);
        let p = programs.get(&name).expect("a loaded program");
        let copies: usize = f[1].parse().unwrap();
        let mut e = Clear::default();
        let ins: Vec<u64> = felts(f[2]).iter().map(|v| e.put(fe_of(v))).collect();
        let masks: Vec<u64> = felts(f[3]).iter().map(|v| e.put(fe_of(v))).collect();
        let before = e.fields.len();
        let got = evaluate(&mut e, p, copies, &ins, &masks);
        match f[4] {
            "ok" => {
                runs += 1;
                let (outs, opened) = got.unwrap_or_else(|err| panic!("{l}: {err}"));
                let values: Vec<[u8; 32]> = outs.iter().map(|&h| bytes_of(&e.get(h).unwrap())).collect();
                assert_eq!(values, felts(f[5]), "{}: outputs", String::from_utf8_lossy(&name));
                assert_eq!(opened, felts(f[6]), "{}: openings", String::from_utf8_lossy(&name));
                // One opening per D/Z row per instance, and nothing else opened.
                assert_eq!(e.opened, copies * p.openings());
                // Only the outputs are new engine values, each its own.
                assert_eq!(e.fields.len(), before + outs.len(), "values left behind");
                let mut distinct = outs.clone();
                distinct.sort();
                distinct.dedup();
                assert_eq!(distinct.len(), outs.len());
                assert!(outs.iter().all(|h| !ins.contains(h) && !masks.contains(h)));
            }
            "abort" => {
                aborts += 1;
                assert!(got.is_err(), "Lean aborts here");
                assert_eq!(e.fields.len(), before, "an abort leaves no value behind");
            }
            other => panic!("{other}"),
        }
    }
    assert_eq!((runs, aborts), (5, 2));
}
