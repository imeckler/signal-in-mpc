This candidate proves actual pinned Prost 0.14.4 `decode_key` on contiguous
`&[u8]` against strict protobuf key validation and a normalized numeric circuit.
Independent acceptance of the new key extraction/bridge remains pending. The
full-varint reference is accepted separately in
`../FullReferenceWork/root-review.json` and is reused within its scoped Buf and
valid-usize indexing model boundary.

Run `python3 SignalReference/ProtoParseWork/KeyReferenceWork/audit.py` to reproduce
provenance, exact metadata selection, pinned Aeneas generation, isolated proof
rebuild and transitive axiom audit. Results are in `proof-report.json`,
`axioms.txt`, and `build.log`.

The actual unchanged validation order is proved: decode a strict u64 varint;
reject values above u32::MAX as InvalidKey; reject wire types6/7 as
InvalidWireType; then reject tag0 as InvalidTag. Success has exact tag=value/8
and wire type=value%8. Noncanonical successful varints up to10 bytes are covered.
Every key-validation error retains the suffix already produced by varint
decoding. Varint errors retain their exact separately proved mutation behavior.

The key circuit produces25 bytes: status255 || consumedBE8 || tagBE8 ||
wireTypeBE8 on success; all25 bytes are zero on error. Its universal numeric AIG
refinement is `LibSignalReference.Candidate.ProstKey.decode_key_refines_artifact`.
The existing `ProtoParse.plan` has exactly the same tag/kind fields; every
actual key error makes its acceptance mask zero for every payload and parser
state (`decode_key_error_rejected`). Payload validation and whole-parser
agreement are separate claims and are not established here.

The proof files are `KeyValue.lean` (actual scalar continuation),
`KeyReference.lean` (complete buffer/refinement semantics), `KeyCircuit.lean`
(key circuit/mapping), `PlanBridge.lean` (existing parser rejection), and
`ArtifactBridge.lean` (complete numeric transport). No generated computational
body is replaced with these specifications.

The explicit extraction boundary is seven reversible unused Step metadata
edits, recorded in `Artifacts/key-step/changes.json`: opaque functions302/306,
trait13/impl21 method slots2/6, and their ordered declarations. Every retained
computational body is identical; retained semantic references do not target
removed slots; slot numbers are unchanged. This remains additional translation
trust for independent review.

No new external model is introduced. `replay.py` reuses the accepted three Buf
wrapper models and all full-varint proofs using deterministic import/namespace
substitutions. `replay-report.json` records every substitution/hash and verifies
that generated Types are identical modulo namespace and all existing generated
computational bodies are byte-identical. Every replayed proof is rebuilt and
audited in the key namespace. Frozen accepted sources are untouched.

The attempted `skip_field` extension is blocked before an actual-function proof
can begin. Original Charon extraction succeeds. After the same structural seven
Step metadata edits (functions311/315, trait13/impl26 slots2/6), pinned Aeneas
exits1 with `Early returns inside of loops are not supported yet`, pointing to
`src/encoding.rs:166-199`, and explicitly ignores the entire skip_field body.
`skip-boundary.json` and `Artifacts/skip-step/aeneas.log` record this result.
Those partial generated files are not compiled, imported or adopted. No
handwritten scalar/group replacement or translator repair is introduced.

No arbitrary segmented Buf, whole Prost parser, Signal security, fixture-runtime,
backend compilation or native MPC execution claim is made by this audit.
