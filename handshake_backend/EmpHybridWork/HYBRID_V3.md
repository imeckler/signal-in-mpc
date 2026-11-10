# Hybrid Boolean/native-field controls on candidate v3 (statistical 128)

Status 2026-11-09. Section 4 of REMAINING_WORK.md, steps 3 and 5, re-run on the validated-v3 Boolean engine. Functional and fault-control evidence on local loopback with fixture secrets. `secure_hybrid_backend` remains `false`.

## Parameter profile

Decided 2026-11-09: malicious security is retained and statistical 128 is the production profile.

| Component | Setting | Where |
|---|---|---|
| Boolean triple buckets | ρ = 128, enforced as a floor in the v3 engine (`EMP_HYBRID_MIN_SSP`) | `prepare_validation_v3.py` |
| Bridge pool cut/bucket check | ρ = 128: bucket 14 / 13 / 12 for 256 / 512 / 1024 kept pairs, cut factor 2 | `dabit_generator.h`, `parameters-128-report.json` |
| Native field engine | security parameter 128; in the MASCOT prime-field path MP-SPDZ reads it only as a minimum field-size guard | `field_engine.cpp` |
| OT extension (Boolean side) | SoftSpoken⟨4⟩ malicious mode; its comments state a fold over F_2^128; not verified line by line | emp-ot `softspoken.cpp` |

The earlier statistical-40 builds and receipts are unchanged; the 128 profile is selected by build flags in `build_hybrid_v3.py`.

## Results (`hybrid-v3-report.json`)

`python3 handshake_backend/EmpHybridWork/build_hybrid_v3.py word-roundtrip curve` then `check_hybrid_v3.py`. All five cases pass:

- Private native-field value → 255 Boolean bits → native field, 510 checked masks; wrong operation counter rejected before the reverse mask opens.
- **First execution of the native X25519 candidate.** Private scalar and point enter as XOR shares, are converted through checked masks, the pinned 9,437-node FieldDag (4,589 multiplications) runs in the field engine, and the result returns as 32 private canonical bytes. Inside MPC it is compared with the value computed independently by the `cryptography` library; only the equality and nonzero bits open. An all-zero point is rejected at the nonzero check and a wrong expectation at the equality check.

The X25519 result bytes stay private and authenticated for a later caller; feeding them into the key schedule is covered further down.

## Cost of one X25519 at this profile (per party, loopback)

| | |
|---|---|
| Wall time | about 7.5 s, of which pool generation 5.8 s and curve 1.6 s |
| Native-field protocol bytes sent | 2.28 GB (excludes TLS framing; includes unused live preprocessing at batch 10,000) |
| Boolean engine bytes, both directions | 7.2 MB |
| Peak memory | about 870 MB |

For comparison the same run with the statistical-40 pool sent 1.20 GB and took about 4.1 s. Pool generation for 1,024 pairs (766 consumed) dominates. This is a single cold run, not a throughput measurement, but at this cost per curve operation the 100,000 sends/hour target depends on established sends needing no curve work and on amortising pools across many operations.

## Cheaper conversion path (candidate)

`curve_fixture_v2.cpp` keeps the scalar's swap bits as field-bit shares, uses full-width masks checked in the Boolean engine, and runs the leaner Lean ladder with a masked inversion. Every gate and field product on this path is a pinned export from Lean. Measured: 0.29 GB native traffic and 1.5 s for the same operation, with five fault cases rejected and a 64-mask batch exercised. Construction, measurements and review points are in [CONVERSION_COST_LEVERS.md](CONVERSION_COST_LEVERS.md).

## Private X25519 into the TLS key schedule (section 4 step 6)

`curve_kdf_fixture.cpp` runs the leaner ladder on XOR-shared scalar and coordinate, converts the result to 255 private Boolean bits, and wires them directly into the Lean handshake-secrets circuit (`TlsKdf.handshakeSecretsFast`, exported by `lower_kdf_circuit.py`) with a public transcript hash. The shared secret is never opened and no host supplies it. The fixture opens two bits only: that the shared secret is nonzero, and that the four derived secrets equal the value computed by an independent HKDF implementation.

Three cases in `check_hybrid_v3.py`: valid; an all-zero shared secret, rejected at the nonzero check; wrong expected secrets, rejected at the equality bit.

Cost of the whole run, per party on loopback: 0.29 GB native field traffic, 651 MB Boolean traffic in both directions together for 1.30 million AND gates (763,185 of them the key schedule), 2.5 s, about 1.2 GB peak memory.

The same fixture built with `EMP_KDF_SIGNAL=1` runs Signal's `RootKey::create_chain`: an XOR-shared root key and the private X25519 result enter `DhRatchet.createCore`; the new root, chain key and status byte stay private. An all-zero agreement is handled inside the circuit (old root kept), so that case succeeds without opening anything about the agreement. Three more cases: valid, zero agreement, wrong expected state.

Both derivations are the wrappers in `TlsMpc/HybridKdf.lean`, which take the 255-bit word exactly as the conversion produces it; the split into little-endian bytes is part of the Lean circuit (`wordBytes_toNat`), so the C++ passes wires through in order. They are compiled by the existing bit-vector compiler and lowered by the shared unverified adapter (`lower_kdf_circuit.py`); they have not been rewritten on the gate-level compiler, and at 763,181 and 554,325 AND gates they are the dominant Boolean cost.

The checker retries a case when a process dies with the OS error "No buffer space available" (kernel socket buffers exhausted by back-to-back loopback runs) and records the retry.

## Not covered

- Authenticated peer/channel binding across the two transports (step 4); both engines run on loopback in one process per party.
- The cross-engine composition argument for the cut/bucket construction, and non-bit and wrong-contribution fault cases at the 128 profile (the earlier fault fixtures were not rebuilt on v3).
- Full-wire byte accounting through the TLS BIO path (step 7), and separating consumed from unused preprocessing.
- Cleanup and erasure on abort.
