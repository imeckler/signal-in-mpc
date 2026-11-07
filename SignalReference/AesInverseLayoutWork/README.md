# Actual AES inverse-layout writer

The selected `aes 0.9.1` function
`soft::fixslice::inv_bitslice::write_reordered` has an Aeneas-to-numeric-circuit
equivalence proof for every 64-bit column and every initial twelve-byte slice.
The result includes the four preserved bytes. Both invocations in the pinned
Rust caller use twelve-byte ranges: `[0..12]` and `[4..16]`.

`Proofs.write_refines_artifact` connects the actual generated Rust function to
the numeric circuit from `Circuit.lean`. All 160 input bits remain secret;
there are 96 output bits, with no AND or XOR operations. `check.py` checked the
six theorem assumption reports and all 160 basis inputs against the actual
byte-write order through both adapter paths. These fixture checks validate
native export; the Lean theorem establishes equivalence for all inputs.

The pinned source is unchanged. The accepted toolchain is Aeneas
`5b9dcf33dccdb1560ea7203ac57ea202476b6ed3`, Charon
`4ad295c1bf982b5533ce7d85f4ddc889ff3127f8`, Rust nightly 2026-08-18,
and Lean 4.31.0. `pins.json` in the parent reference package identifies the
locked `libsignal 0.106.1` dependency archive and source hashes.

The whole `inv_bitslice` wrapper does **not** yet have a completed reference
or equivalence proof:

- Plain extraction fails while lifting `hybrid_array::traits::ArraySize` GATs.
- Excluding that unused trait metadata allows Charon to finish, but Aeneas's
  array-default preprocessing fails on the wrapper's hybrid-array metadata.
- Monomorphizing that profile gets further, but leaves actual library
  default/index operations opaque and fails during variable-name extraction
  (`Charon.TypesUtils.as_ident`). Its external templates are unaccepted.

`select_write.py` makes an additional, explicitly trusted declaration-selection
step from the complete non-monomorphized Charon output. It retains the actual
nested writer's source, signature, and body exactly. That function is closed:
its only calls are eight builtin mutable slice indices, and it has no user
type, function, trait, or global dependencies. Every discarded declaration and
the changed declaration order are recorded reversibly in
`Artifacts/WriteReordered/selection-changes.json`; the compact `review.json`
hash-pins that file. An independent review is recorded at
`../AesKeyScheduleWork/inverse-writer-selection-review.json`.

Trust boundaries are the reviewed Charon/Aeneas translation and declaration
selection, the pinned Aeneas scalar/slice models, Lean's kernel and its three
standard foundational axioms, and the unverified native exporter and MPC
backend. There are no handwritten replacement Rust functions, custom crypto
models, custom axioms, incomplete proof placeholders, or native-decision
proofs. No native multi-party execution was performed for this wiring artifact.

Remaining wrapper work includes hybrid-array allocation/default/index
operations, subrange borrow write-back, and composition of the inverse
transpose with the eight writer calls and block relabeling. This leaf does not
establish whole AES, AES-CBC, or Signal send-path equivalence.

`wrapper-boundary-report.json` preserves three subsequent full-wrapper probes
and their exact source, LLBC, log and harness hashes. Including actual
hybrid-array bodies reaches its mutable `Guard`/`MaybeUninit` allocation graph,
which pinned Aeneas rejects. `OptimizedProbe/` uses existing Rust MIR inlining
and GVN passes on the unchanged source; the same Guard remains. The more
aggressive `ScalarizedProbe/` additionally enables existing scalar replacement
and raises inlining thresholds; pinned Charon rejects union constants and
`ConstEvalVal` values. Both profiles retain debug assertions and overflow
checks. Neither is accepted, and neither alters the accepted extraction or
standard models.

The remaining boundary needs translator support for those actual operations,
or an explicitly reviewed transparent library model with its own documented
trust boundary. Removing the computational calls as metadata or assuming
successful return would not complete the wrapper equivalence.

Reproduce the accepted leaf:

```sh
python3 SignalReference/AesInverseLayoutWork/extract_inverse.py InvBitsliceScoped
# The full-wrapper Aeneas failure here is expected; Charon output is complete.
python3 SignalReference/AesInverseLayoutWork/select_write.py
python3 SignalReference/AesInverseLayoutWork/check.py \
  --packages-dir /Users/izzy/repos/eco-theorem-combined/.lake/packages
```
