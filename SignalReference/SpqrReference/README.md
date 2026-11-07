# Actual SPQR serialization reference work

The completed proof slice is SPQR 1.6.0's real `src/lib.rs::encode_varint`,
at the libsignal-locked commit
`06959b4708f9b7b1e94d0f8cc835f3958c077e94`.

Run `python3 SignalReference/SpqrReference/check.py` to rebuild and audit its
21 proof endpoints. The actual loop and length constant were extracted by the
accepted Charon/Aeneas toolchain. `select_varint.py` applies seven reversible
edits to unused Step dictionary metadata; all computational declarations remain
identical. Selection correctness is a reviewed trust boundary, not a mechanized
proof. A separate independent acceptance record is required.

Import `SpqrReference.VarintCircuit`. The namespace is
`LibSignalReference.Candidate.SpqrVarint`:

- `encode_eq_run` preserves the complete translated result, including Vec.push
  failures and divergence, without assuming success.
- `encode_appends` proves actual emitted bytes for every U64 within the official
  model's `buffer.length + 10 ≤ Usize.max` bound.
- `encode_uint64`, `uint64_refines_artifact` and
  `uint64_guarded_refines_artifact` connect the actual operation to the root
  64-bit MPC circuit, including every output bit and the guarded success byte.
  The public width must be canonical and between 1 and 10; values stay secret.
- `encode_uint32` also covers the widened message-index input against the
  existing 32-bit circuit at canonical widths 1 through 5.

The source's `hax_lib::assume!` calls introduce no proof assumptions: ordinary
Rust builds select the actual dummy macro, which expands to unit. The pinned
macro sources, unchanged standard models, extraction graph and proof
dependencies are checked and recorded in `proof-report.json`. Cargo's git
checksum map is empty; the audit instead compares all 99 upstream archive
files byte-for-byte against the pinned SPQR commit archive. The only extra
vendor file is Cargo's checksum metadata itself.

The complete `Message::serialize` reference is **not finished**. The actual
shared `&chunk.data[..]` indexing operation pulls a RangeFull SliceIndex
dictionary whose mutable methods are unsupported by the pinned translator.
`SharedIndexProbe` preserves every body and omits only those uncalled methods;
Aeneas emits it, but Lean rejects the incomplete official six-field record.
It is an expected failure, not an accepted implementation or custom model.
The monomorphized and optimized-MIR alternatives also fail. Exact profiles,
logs and exclusions are recorded in `serializer-boundary-report.json`.

All `Generated/`, `GeneratedSelected*`, `Selected*` and `SharedIndexProbe`
outputs are diagnostic and unaccepted. Only `VarintGenerated/`,
`VarintSelected/`, `VarintReference.lean` and `VarintCircuit.lean` participate
in the completed proof audit. No external template is filled or imported.
This work does not establish the SPQR state machine, KEM, chain updates,
whole Signal serialization, or cryptographic security.
