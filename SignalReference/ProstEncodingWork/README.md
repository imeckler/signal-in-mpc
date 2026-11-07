# Actual Prost varint refinement

`CircuitBridge.uint32_refines_artifact` proves that every numeric MPC output
bit equals the bytes appended by the translated actual Prost varint encoder,
using the actual selected `Vec<u8>` buffer methods. It covers all uint32 values
and every public width from 1 through 5 that passes the secret canonical-width
guard. The buffer must satisfy `buf.length + 10 <= Usize.max` in the accepted
Aeneas standard model.

Import `ProstEncodingWork.CircuitBridge`. The proof namespace is
`LibSignalReference.Candidate.ProstEncoding`; the name records its isolated
package location, while `check-report.json` records the accepted selected scope.

The useful endpoints are:

- `Reference.encode_eq_run`: exact behavior of the actual generic loop,
  preserving any success, failure, or divergence from its buffer dictionary.
- `NatBridge.encode_appends_within`: the loop equals the root Lean public-length
  encoder under an explicit bounded append contract.
- `VecBridge.put_slice_success` and `put_slice_overflow`: behavior of the actual
  selected `bytes` Vec override through the official Aeneas Vec model.
- `VecBridge.vec_put_u8_default`: the assembled dictionary's one-byte operation
  equals the translated actual default method.
- `VecBridge.vec_encode_appends`: the bounded append contract is discharged for
  those concrete methods, for every uint64 value.
- `CircuitBridge.canonical_width_bounds` and `encode_publicNat`: the secret
  width guard and fixed-width byte circuit select the actual canonical varint.
- `CircuitBridge.vec_encode_uint32` and `uint32_refines_artifact`: exact appended
  bytes, then the numeric compiled output-bit equality.

All theorem names above have the common namespace; filenames indicate imports,
not additional namespace components.

The actual sources are libsignal 0.106.1 commit
`904c8dc8216073b078a5f2f5090e3da8382e6a92`'s locked `prost` 0.14.4 and `bytes`
1.12.0. `extract.py` selects unchanged functions through the pinned
Charon/Aeneas toolchain. The accepted generated modules are `EncodeSelected`
and `VecPutSlice`; neither contains an external template or custom model.

The generic extraction needs an independently reviewed compatibility step:
eleven reversible changes omit unused iterator slots, unused BufMut fields,
and unused opaque code-generation roots. Every retained computational body is
unchanged. The declared default for `put_slice` remains in LLBC metadata, and
the actual dictionary calls remain in the translated loop and default method.
The selection itself is trusted, not mechanized. The independent review is
`../prost-selection-independent-review.json`.

Concrete dispatch is checked against the actual Vec implementation's LLBC:
slot 5 selects its real `put_slice` override; slot 7 inherits the real
`put_u8` default. The local and cross-crate default definitions have the same
pinned source identity and body range. Their raw MIR differs by a local
borrow-check FakeRead, so this package does not assert byte-identical raw bodies
across those two extraction profiles. The proof uses the unchanged translated
cross-crate default and the unchanged translated Vec override.

Run:

```sh
python3 SignalReference/ProstEncodingWork/check.py
```

This verifies pins, source identities, actual dispatch, the reviewed selection,
generated-file hashes and all 35 theorem endpoints. It rebuilds the selected
Lean references and proofs, but does not rerun extraction or native MPC. Only
`propext`, `Classical.choice`, and `Quot.sound` are permitted assumptions. The
128-byte continuation identity uses kernel reduction rather than native proof
evaluation. No backend compilation or network benchmark was performed here.

Whole `SignalMessage::new`, derived message encoding, and field-wrapper
composition remain separate obligations. The diagnostic `Length` profile for
`encoded_len_varint` still has unsupported `NonZeroU64` construction/logarithm
templates and is not accepted. Other diagnostic generated directories are
excluded from the proof imports and accepted audit. Extraction, official
standard-library models, native serialization, and backend execution remain
the previously declared trust boundary.
