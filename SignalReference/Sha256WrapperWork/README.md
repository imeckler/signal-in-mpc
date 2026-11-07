# Actual SHA core initialization and wrapper boundary

`Initial.lean` proves the actual pinned `sha2 0.11.0`
`Sha256VarCore::new` operation, including the 28-byte, 32-byte and invalid-size
branches. Its SHA-256 state equals the initialization already used by the Lean
circuits. `initial_compression_refines_artifact` then composes that constructor
with the previously accepted actual `compress_u32` implementation and proves
every numeric MPC output bit for arbitrary sixteen shared input words.

This is a constructor-plus-compression theorem. It does **not** prove the actual
`Digest`, `update`, `finalize`, block-buffer, byte-loading or output-copy wrappers.
It assumes no opaque hash or buffer contract. The eight endpoints in `Checks.lean`
pass with only the standard foundational axioms `propext`, `Classical.choice`
and `Quot.sound`.

The extraction uses accepted Aeneas `5b9dcf33dccdb1560ea7203ac57ea202476b6ed3`,
Charon `4ad295c1bf982b5533ce7d85f4ddc889ff3127f8`, Rust nightly2026-08-18 and
Lean4.31.0. The SHA flags select the portable compact backend. No Rust source,
accepted translator or standard model is modified. The package configuration
has sha2 default/alloc/oid features and no zeroize; the emitted empty Drop path
therefore makes no erasure guarantee.

`select_initial.py` performs three exact, reversible deletions of unused
`ArraySize` implementation metadata. The corresponding trait declaration was
already excluded to avoid Charon's unsupported GAT lifting. All ten original
ordered roots, computational bodies, signatures and constants remain unchanged.
The selected computational closure uses function IDs **0,15,16,17,161**, types
**0,1,2**, and globals **1,2**. `typed-dependency-closure.json` describes their
signatures and edges. Other, non-emitted declarations remain diagnostic metadata;
their references to the removed entries are explicitly listed. They are outside
this reference claim. The selection is an additional trusted preprocessing step,
pending independent review and a separate acceptance record.

`check.py` verifies all five locked registry archives against `Cargo.lock`,
compares every archived upstream source file byte-for-byte, verifies all87
official Aeneas standard-model files against the pinned source archive, rebuilds
the selected Lean files, and audits all eight theorem endpoints. The complete
source and tool hashes are in `proof-report.json`.

Reproduce the selected proof slice:

```sh
python3 SignalReference/Sha256WrapperWork/extract.py core_new_closed --charon-only
python3 SignalReference/Sha256WrapperWork/select_initial.py
python3 SignalReference/Sha256WrapperWork/check.py
```

Direct actual core-update/core-finalize extraction gets through Charon after the
ArraySize exclusion but fails Aeneas's array-default metadata prepass. Direct
complete `Sha256::update` and `finalize_into` graphs fail Charon GAT lifting.
`wrapper-boundary-report.json` records these exact failures, the earlier root
selection diagnostics, and separate source-level obligations. The latter include
raw buffer writes and MaybeUninit exposure, ResetGuard error behavior, actual
byte-to-word loading, length arithmetic, and mutable iterator output copying.
Those are unproved dependencies; they are not additional translator failures
observed by this probe. The existing `ShaWordsWork` closure result also retains
its explicit unresolved Formatter type boundary.

Regenerate the boundary inventory without changing any proof or model:

```sh
python3 SignalReference/Sha256WrapperWork/record_boundaries.py
```
