# Actual SignalMessage encoding extraction

This directory selects the actual generated
`{prost::message::Message for libsignal_protocol::proto::wire::SignalMessage}::encode_raw`
from pinned libsignal `904c8dc8216073b078a5f2f5090e3da8382e6a92`, built with its
locked Prost 0.14.4 and bytes 1.12.0 dependencies. No Rust source is substituted
or modified. The generated wire type comes from the actual `wire.proto` build
step and the encoder comes from the actual Prost derive macro.

The whole-message profiles here remain **unaccepted candidates**. An Aeneas output containing
external templates is not a completed reference refinement. The full Lean
send circuit is implemented and tested separately in `TlsMpc/Signal/Send.lean`.

Run from the workspace root:

```sh
python3 SignalReference/SignalMessageWork/extract.py WireEncode
python3 SignalReference/SignalMessageWork/extract.py WireEncodeFields
python3 SignalReference/SignalMessageWork/extract.py WireEncodeFieldsFull
```

`WireEncode` successfully translates the selected generated encoder. Its body
encodes six optional fields in tag order, including `Some(0)` scalar counters.
External obligations remain for actual bytes/uint32 encoders and the concrete
Vec BytesAdapter dictionary. Generated templates are intentionally left
unfilled and excluded from accepted proof imports.

`WireEncodeFields` includes actual bytes and uint32 encoders, encode_key,
encode_varint, the Vec BytesAdapter length/append methods, and the BufMut byte
default. It reaches the pinned Aeneas model mismatch for the two unused newer
`Step` overflow fields. The separate reviewed varint selection in
`ProstEncodingWork` addresses its own exact graph; its review does not
automatically approve modifying this larger graph.

`WireEncodeFieldsFull` additionally selects actual Vec default, slice Buf
methods, tag constants and range helpers. Its translation exposes two further
failures:

- `Vec::default` reaches a `transmute<Alignment, NonNull<u8>>` in the inlined
  allocation representation that Aeneas cannot translate. This default belongs
  to an unused BytesAdapter supertrait dependency; any removal requires a
  separate closed-dependency review.
- The actual `Buf for &[u8]::advance` fails with
  `evaluate_function_symbolic ... Unexpected result: Cps.Unit`, at
  `bytes-1.12.0/src/buf/buf_impl.rs:2906`. It changes `&mut &[u8]` to the suffix
  after checking the requested count. This operation is relevant to concrete
  buffer composition and cannot simply be omitted as unused.

The actual Vec BytesAdapter's `append_to` calls `BufMut::put(self.as_slice())`,
not `put_slice`. Actual bytes Vec `put` reserves capacity, loops over source
chunks, calls `Vec::extend_from_slice`, and advances the source buffer. The
already proved varint `put_slice` path therefore does not by itself discharge
byte-field encoding. Completing the slice-borrow translation or a faithful
alternative extraction profile is required for this composition.

Each profile records source hashes, tool versions, exact commands, selected
declarations, exclusions and external obligations in `Artifacts/*/inventory.json`.
No custom crypto or buffer axioms, patched source bodies, or completed
whole-message equivalence claims are introduced here.

## Accepted counter-field slice

`UInt32Field` / reviewed `UInt32Selected` select actual
`prost::encoding::uint32::encode`, `encode_key`, the varint loop, the byte
default, tag constants and range-check helpers. The unchanged official Aeneas
`RangeInclusive.new` standard model is used; including the actual constructor
body simultaneously with that existing model exposed a pure/Result signature
mismatch and is not part of this accepted graph.

`UInt32Reference.field_refines_artifact` proves both Signal counter fields,
tags 2 and 3, through every numeric output bit, for all uint32 values and
canonical public widths 1–5. It instantiates actual Vec append semantics from
`ProstEncodingWork`, with `buffer.length + 11 ≤ Usize.max`. Thus the actual tag
check, wire discriminant, tag byte, value varint and appending behavior are
covered together. This does not claim all of SignalMessage::new is refined.

Reproduce with `python3 SignalReference/SignalMessageWork/check_uint32.py`.
`uint32-proof-check.json` audits eight endpoints with only the standard
foundational axioms. The independently reviewed selection has ten reversible
dead-metadata changes and ten unchanged computational declarations; its review
is `../ProstEncodingWork/UInt32SelectionReview/review.json`. No generated Lean
body, Rust source or standard model was patched.
