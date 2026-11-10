# PreKey constructor: scoped actual-source reference

This candidate extracts unchanged libsignal v0.106.1 (`904c8dc8216073b078a5f2f5090e3da8382e6a92`), using the pinned Charon and Aeneas release. It proves the actual generated `PreKeyBundleContent::try_from` control flow and `PreKeyBundle::new` payload construction, **relative to explicit external models**. It is not a complete actual-Aeneas refinement of the Rust dependency closure.

`Proofs.lean` has eight kernel-checked endpoints. `constructor_exact` preserves every required payload and the optional ID/key pair. `try_from_present` covers arbitrary required payloads and all four optional-presence cases; its successful reduction does not execute any missing-field callback. `try_from_source_spec` proves required-field error order against the declared error models. `first_missing_refines` and `optional_mask_refines` connect that behavior to the frozen shared `TlsMpc.Signal.PreKeyBundle` component. The two Option model laws distinguish the callback-free success case and pair semantics.

The default feature profile is Kyber1024. Required fields are checked in source order: registration, device, signed ID, signed public key, signed signature, PQ ID, PQ public key, PQ signature, identity. Mismatched optional ID/key presence is discarded. All registration/key IDs retain the entire `u32`; the constructor does not add value checks. Public keys, signature vectors, and identity are preserved, without signature verification. A typed `DeviceId` supplied by real libsignal has value 1–127; our external NonZero representation preserves the positive byte and the constructor never inspects it. Arbitrary hand-constructed Lean values outside that typed-input invariant are not claims about Rust API inputs. Likewise, real typed Kyber1024 public keys have 1,568 payload bytes; parsing, raw wire encodings and key validity are prior boundaries.

## Explicit model boundary

The generated `Types.lean` and `Funs.lean` are unedited Aeneas outputs. `TypesExternal.lean` and `FunsExternal.lean` are handwritten models matching the generated templates:

- `Option::zip` and `Option::ok_or_else` model the exact simple matches in the pinned Rust sysroot. They are **not** actual Aeneas translations of those standard-library bodies.
- `NonZeroU8Inner` is a nonzero byte subtype; `NonZero<T,Inner>` retains its inner value. The translator cannot currently translate the actual Rust niche range type.
- `SignalProtocolError` represents only the `InvalidArgument(String)` output reachable from this constructor. It is not a model of the complete protocol error enum, whose callback-error variant contains an unsupported dynamic trait object.
- Nine missing-field closure models return the exact source strings. String allocation and full error-enum refinement are not proved. Error-order results are conditional on these models. The all-required-present result does not call them.
- The Kyber1024 public `key_length` model returns 1,568. It is present through a trait dependency and is not invoked by any proved constructor behavior.

No validation Boolean is substituted for cryptography. This work contains no signature checking, trust-store policy, async session behavior, PQXDH status wiring, backend adapter or native MPC execution. There are zero new circuit gates or backend artifacts. The existing frozen constructor compiler theorem remains unchanged; the new reference endpoints connect its `firstMissing`/`optionalMask` semantics to the generated source behavior, rather than claiming a new end-to-end MPC theorem.

## Evidence and reproduction

```sh
python3 SignalReference/PreKeyReferenceWork/extract.py ContentModels
python3 SignalReference/PreKeyReferenceWork/check.py
python3 SignalReference/PreKeyReferenceWork/freeze.py
```

Extraction uses its own `Build/Charon` Cargo target, locked offline dependencies, unmodified Rust, and no LLBC transformation. `Artifacts/ContentModels/inventory.json` contains the exact selection/opacity commands, pinned tool versions, original-source hashes, LLBC hash, generated hashes and declaration inventory. That LLBC contains 34 types and 44 functions (21 structured, 23 opaque); the dependency inventory is broader than the proved runtime slice.

`build.py` compiles to `Build/Lean` with existing pinned dependency caches, without Lake dependency resolution or downloads. Its cache location is explicit. An initial plain `lake build` attempted dependency resolution and failed on unavailable network; the successful workflow is fully offline. `check.py` compares every pinned Aeneas Lean model source with the verified release archive, recompiles the isolated modules, and audits every endpoint using `#print axioms`. Only `propext`, `Classical.choice`, and `Quot.sound` occur; no imported template holes or custom axioms support a theorem.

`differential-cases.json` records all 2,048 presence combinations evaluated through the actual generated Lean control flow and compared with the frozen unchanged Rust constructor oracle. The oracle binary is checked against its frozen receipt. Fixtures use valid typed zero-byte EC/identity and Kyber public encodings, empty signature vectors, device 127, and full-width registration/ID values. This confirms the constructor imposes no signature or small-order policy. These fixtures are not cryptographically accepted session inputs. The differential compares missing-field code, optional presence, and successful metadata; universal key/signature payload preservation is supplied by the kernel theorem, not by that native comparison.

`check.py` also verifies every file in both frozen XEdDSA and PreKey completion manifests. Neither checkpoint is changed. `report.json`, `axioms.txt`, and `completion.json` identify the checked scope and exact frozen files.

## Preserved diagnostics

The other extraction profiles are diagnostics, not accepted reference results. Unscoped construction reaches unrelated KEM trait cycles and the dynamic error variant. Omitting the explicit `core::convert::TryFrom` include causes Aeneas to prune the selected implementation; the successful profile asserts the actual definition is emitted. Actual `ok_or_else` fails on an unexpected unit constant in `FnOnce`; actual generic **and monomorphic** `zip` fail with “There should be no bottoms in the value.” Actual NonZero extraction fails on the niche range pattern type. Exact logs and inventories remain under `Artifacts/`.

A useful next independent gap is repairing the pinned translator's Option wildcard/drop handling in a separate translator candidate, starting from the preserved monomorphic `ContentZipMono` LLBC. That could remove the `zip` model without touching cryptography or frozen work. The `FnOnce` unit-call and dynamic error/string boundaries remain separate obligations.
