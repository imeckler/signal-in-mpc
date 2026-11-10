# Actual XEdDSA public-key field decoding

This candidate closes a narrow actual-source reference gap: pinned dalek's serial/u64 `FieldElement51::from_bytes` and its nested `load8_at`, which are used by `MontgomeryPoint::to_edwards` in libsignal's XEdDSA verifier. Both functions are extracted unchanged with pinned Charon/Aeneas. There are no custom external models, generated-code edits, LLBC rewrites, translator patches, or supplied cryptographic-validity flags.

The kernel proves that the decoder always returns five limbs below `2^51`, whose represented integer is the little-endian 32-byte input modulo `2^255`. Reducing that integer modulo `2^255-19` exactly supplies the frozen recovery circuit's field input. `RecoveryInput.compiled_recovery_input` combines this actual decoder theorem with the existing shared recovery compiler theorem. Its conclusion concerns the frozen circuit's recovery formulas; it does **not** claim those formulas are already proved equivalent to the rest of dalek's `to_edwards` implementation.

`high_bit_ignored` proves bit255 is ignored, and `noncanonical_reduction` proves the nineteen low255-bit encodings `p` through `p+18` represent `0` through `18`. There is no canonical-encoding rejection. `actual_decode_field_alias` proves equal field representations for any pair of field-equivalent byte inputs, and `compiled_recovery_field_alias` proves that every compiled recovery output respects those aliases. Field normalization is distinct from point validity: zero, small-order and twist inputs are not declared valid signatures. The separate signature sign bit is not part of this decoder.

## BAF reuse

The reviewed BAF dalek fork is `95b5831c63ff1c5f6287bd3a77569412a9afdbfb`. Although its entire `field.rs` differs from our locked dalek 5.0.0 source, the selected `from_bytes` function, including `load8_at`, is byte-identical. `provenance.py` verifies that fact and verifies selected proof/source files against the previously reviewed archive hash.

`BafSupport.lean` contains the needed pure indexing, radix-sum and bit-mask lemmas. `FieldDecodeProof.lean` adapts BAF's actual `FromBytes.lean` proof to our exact generated functions, namespaces, pinned Lean 4.31 and Aeneas release. `baf-port.diff` records the proof-file changes. A local finite-sum `Array.asNat` definition and explicit five-limb interpretation avoid importing the full external model tree. The dependent finite-range rewrite and `Array.make` simplification are compatibility changes, all checked by Lean. No BAF `RustAx`, Subtle, field arithmetic or cryptographic contract is imported. Apache-2.0 notices are retained; this is not a reproduced full BAF build.

## Evidence

- `Artifacts/FieldDecode/inventory.json`: exact selected-source hashes, pinned tool versions, selection command, original LLBC hash and generated hashes.
- `Generated/FieldDecode/{Types,Funs}.lean`: unedited outputs; two actual function bodies and no external templates.
- `FieldDecodeProof.lean`: actual byte-decoder totality, integer interpretation and limb bounds.
- `RecoveryInput.lean`: field normalization and frozen recovery compiler input bridge.
- `report.json`, `axioms.txt`: all seventeen public helper/reference/bridge endpoints audited; only standard Lean axioms are allowed.
- `fixtures.json`: generated-decoder arithmetic checks and native original/normalized recovery comparisons, including all single-bit positions, all nineteen noncanonical representatives, zero/one, high-bit aliases and deterministic random values.

The native test invokes the existing unchanged, hash-verified dalek oracle's public `MontgomeryPoint::to_edwards` operation for signs 0 and 1, comparing each original encoding with the canonical field encoding computed from the actual generated decoder. It does not expose dalek's private limbs and is not presented as a direct native private-function test. The universal limb-value result is the kernel theorem.

No new circuits or backend artifacts are emitted: the new gate count is zero. Private byte/field conversion execution, full dalek point-recovery refinement, challenge SHA512/reduction, double-scalar multiplication, whole XEdDSA verification and native MPC execution remain outside this checkpoint. All frozen XEdDSA, PreKey and PreKeyReference checkpoint files are verified unchanged.

From the repository root:

```sh
python3 SignalReference/XEdDsaReferenceWork/extract.py FieldDecode
python3 SignalReference/XEdDsaReferenceWork/check.py
python3 SignalReference/XEdDsaReferenceWork/freeze.py
```

`Build/Charon` and `Build/Lean` are isolated. The Lean build uses explicit existing dependency caches without network resolution. `check.py` checks all pinned Aeneas Lean source files against the release archive before building. `completion.json` freezes the candidate's exact files; acceptance and Git integration remain with the parent.

The checkpoint trusts the pinned Charon/Aeneas translation and the Lean kernel, including the audited standard Lean axioms. It does not prove correctness of the Rust compiler or translator. The freeze receipt remains a candidate record, not acceptance or an application readiness signal.
