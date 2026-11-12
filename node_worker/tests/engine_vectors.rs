//! Rust against Lean: every vector of tests/engine_vectors.txt (computed by the Lean definitions
//! in TlsMpc/Node/Engine.lean, through tests/lean/EngineVectors.lean) is decoded, re-encoded,
//! reduced to its skeleton and checked here, and each result must equal Lean's byte for byte:
//! `decodeBatch` / `encodeBatch` (round trip), `skeletonBytes`, `check` over the batch (the
//! verdict, the refused index, every reply shape) and the context after it (carried across the
//! batches of a case; `checkBatch` includes decision D8 and the width bounds), `decodeBatch` on
//! malformed inputs, `agreedBytes` (the agreement on usable and unusable batches), and
//! `encodeReplies`.
mod common;

use common::{hex, unhex};
use node_worker::handles::{Ctx, Shape, check_batch};
use node_worker::interp::{
    Party, Wire, agreed_bytes, decode_batch, decode_replies, encode_batch, encode_replies, skeleton_bytes, usable_batch,
};
use sha2::{Digest, Sha256};
use std::collections::BTreeSet;

fn shapes_text(shapes: &[Shape]) -> String {
    if shapes.is_empty() {
        return "-".into();
    }
    shapes
        .iter()
        .map(|s| match s {
            Shape::Unit => "u".to_string(),
            Shape::Bits(n) => format!("b{n}"),
            Shape::Elems(n) => format!("e{n}"),
            Shape::Bytes(n) => format!("x{n}"),
        })
        .collect::<Vec<_>>()
        .join(",")
}

fn opcode(w: &Wire) -> u8 {
    encode_batch(std::slice::from_ref(w))[8]
}

#[test]
fn rust_equals_lean_on_every_vector() {
    let text = common::text();
    let sig_table = common::sigs(&text);
    assert_eq!(sig_table.len(), 5);
    let sigs = |n: &[u8]| sig_table.iter().find(|(k, _)| k == n).map(|(_, s)| s.clone());

    // State: the context per party (a case uses slot 0), the batch under test, and the outcome
    // of `check` on it.
    let mut ctx = [Ctx::default(), Ctx::default()];
    let mut party = 0usize;
    let mut batch: Vec<Wire> = vec![];
    let mut outcome: Option<Result<(Ctx, Vec<Shape>), usize>> = None;
    let mut skeletons_by_case: Vec<(String, Vec<String>)> = vec![];
    let mut round_skeleton: Option<String> = None;
    let mut in_flow = false;
    let mut opcodes = BTreeSet::new();
    let (mut batches, mut refusals, mut decodes, mut replies, mut flows, mut cases) = (0, 0, 0, 0, 0, 0);
    let (mut agreed, mut unusable) = (0, 0);

    for (number, line) in text.lines().enumerate() {
        let at = format!("engine_vectors.txt line {}", number + 1);
        let (key, rest) = line.split_once(' ').unwrap_or((line, ""));
        match key {
            "sig" => {}
            "sha256-abc" => assert_eq!(rest, hex(&Sha256::digest(b"abc")), "{at}: the Lean SHA-256 used by the flows"),
            "case" => {
                cases += 1;
                ctx = [Ctx::default(), Ctx::default()];
                party = 0;
                skeletons_by_case.push((rest.to_string(), vec![]));
            }
            "flow" => {
                flows += 1;
                in_flow = true;
                ctx = [Ctx::default(), Ctx::default()];
                skeletons_by_case.push((format!("flow {rest}"), vec![]));
            }
            "round" => round_skeleton = None,
            "party" => party = if rest == "a" { 0 } else { 1 },
            "batch" => {
                batches += 1;
                let bytes = unhex(rest);
                batch = decode_batch(&bytes).unwrap_or_else(|| panic!("{at}: Lean's encodeBatch does not decode"));
                assert_eq!(hex(&encode_batch(&batch)), rest, "{at}: round trip");
                opcodes.extend(batch.iter().map(opcode));
                outcome = Some(check_batch(&sigs, &ctx[party], &batch));
            }
            "skeleton" => {
                assert_eq!(hex(&skeleton_bytes(&batch)), rest, "{at}: skeletonBytes");
                let blank: Vec<Wire> = batch.iter().map(Wire::blank).collect();
                assert_eq!(decode_batch(&unhex(rest)), Some(blank), "{at}: the skeleton decodes to the blanked batch");
                skeletons_by_case.last_mut().unwrap().1.push(rest.to_string());
                // Both parties of a flow round agree on the same skeleton.
                if in_flow {
                    match &round_skeleton {
                        Some(s) => assert_eq!(s, rest, "{at}: the parties' skeletons differ"),
                        None => round_skeleton = Some(rest.to_string()),
                    }
                }
            }
            "verdict" => {
                let got = outcome.as_ref().expect("a batch before its verdict");
                match (rest.split_once(' ').unwrap(), got) {
                    (("ok", shapes), Ok((_, s))) => assert_eq!(shapes_text(s), shapes, "{at}: shapes"),
                    (("refused", index), Err(i)) => {
                        refusals += 1;
                        assert_eq!(i.to_string(), index, "{at}: refused index");
                    }
                    (want, got) => panic!("{at}: Lean says {want:?}, Rust says {:?}", got.as_ref().map(|r| shapes_text(&r.1))),
                }
            }
            "ctx" => {
                let after = match outcome.take().expect("a batch before its context") {
                    Ok((c, _)) => c,
                    Err(_) => ctx[party].clone(),
                };
                assert_eq!(after.canonical(), rest, "{at}: context after the batch");
                ctx[party] = after;
            }
            "decode" => {
                decodes += 1;
                let f: Vec<&str> = line.split(' ').collect();
                let got = decode_batch(&unhex(f[1]));
                match f[2] {
                    "none" => assert_eq!(got, None, "{at}: Lean refuses this input"),
                    "some" => assert_eq!(got.map(|b| hex(&encode_batch(&b))).as_deref(), Some(f[3]), "{at}: decodeBatch"),
                    other => panic!("{at}: {other}"),
                }
            }
            "agreed" => {
                agreed += 1;
                let f: Vec<&str> = line.split(' ').collect();
                let me = if f[1] == "a" { Party::A } else { Party::B };
                let usable = usable_batch(me, &unhex(f[2]));
                if usable.is_err() {
                    unusable += 1;
                }
                assert_eq!(hex(&agreed_bytes(&usable)), f[3], "{at}: agreedBytes");
            }
            "reply" | "replies" => {
                replies += 1;
                let items = decode_replies(&unhex(rest)).unwrap_or_else(|| panic!("{at}: Lean's encodeReplies does not decode"));
                assert_eq!(hex(&encode_replies(&items)), rest, "{at}: encodeReplies");
            }
            "end" | "endflow" | "result" => {}
            other => panic!("{at}: unknown key {other}"),
        }
    }

    // The two parties' wires of the same instructions have the same skeletons.
    let skel = |name: &str| skeletons_by_case.iter().find(|(n, _)| n == name).unwrap().1.clone();
    assert_eq!(skel("all-a"), skel("all-b"));
    assert!(opcodes == (1..=21).collect::<BTreeSet<u8>>(), "every opcode is covered: {opcodes:?}");
    // Every vector was looked at (counts as generated; see s9r_vectors.py's summary).
    assert_eq!((cases, flows, agreed, unusable), (98, 5, 18, 9));
    assert!(batches >= 137 && refusals >= 74 && decodes >= 26 && replies >= 19, "{batches} {refusals} {decodes} {replies}");
    eprintln!(
        "lean vectors: {cases} cases, {flows} flows, {batches} batches ({refusals} refused), {decodes} decoder inputs, \
         {agreed} agreements ({unusable} unusable), {replies} reply encodings"
    );
}
