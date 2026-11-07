# Actual AES-256 key-schedule equivalence

`FullSchedule.lean` proves the numeric MPC circuit equal to the unchanged
`aes@0.9.1` software `aes256_key_schedule` selected from pinned libsignal's
Cargo dependency graph. The theorem covers every 32-byte key and all 120
output words, including checked arithmetic, indexing, mutable borrow
write-back, both expansion branches, phase conversions, NOT restoration and
the final iterator exit. All 256 input bits and 7,680 output bits remain secret.

The final endpoint is
`LibSignalReference.Candidate.AesKeySchedule.key_schedule_refines_artifact`.
`key_schedule_all_arrays` covers every actual Aeneas fixed-size key array.
The proof consumes the actual generated entrypoint; it has no cryptographic
stubs, source substitutions, custom computational models or custom axioms.
The historical `Candidate` namespace is retained to keep dependent files stable.

`schedule-proof-check.json` records the complete source/model audit and 37
checked theorem endpoints. Only Lean's `propext`, `Classical.choice` and
`Quot.sound` occur. It also records 16 public fixtures evaluated by the actual
translated entrypoint and compared against both numeric adapter paths.
Fixtures supplement the universal proof and check the unverified exporter.

The exported artifact uses 1,664 AND gates and 8,860 XOR gates after generic
adapter simplification. `schedule-backend-check.json` records five-party
MP-SPDZ v0.4.4 compilation at batches 1 and 16, using 1,664 and 26,624 bit
triples respectively, and checks all public fixture outputs in the clear
MPC-source harness. The compiler sources match the pinned official archive.
These checks do not execute networked MPC or measure throughput.

## Reference and trust boundary

The original translation failed because Aeneas's `Iterator` dictionary lacks
the `rev` field. Its standard library does contain the standalone reverse
constructor, reverse iterator and range `next_back` models. Selected calls use
the standalone constructor. `inspect_metadata.py` removes only unused
dictionary slots and two unused `Step` overflow declarations. It retains the
actual called reverse constructor, its default-method provenance and all 18
structured computational bodies without modification.

This extraction preprocessing is trusted, not mechanized. The selector pins
the complete input up to diagnostic-name ordering, checks the reversible
12-change diff and full retained semantic reference graph, and permits only
the reviewed retained default-method provenance. The independent review is
`../AesInverseLayoutWork/key-schedule-metadata-review.json`; `review.json`
records the source/output hashes. Its historical candidate flags describe
the extraction step; the later completed refinement is recorded in
`schedule-proof-check.json`.

The selected implementation is the portable software backend, selected using
`aes_backend="soft"`. This proof does not establish equivalence to hardware
backends or the dispatch wrapper. Rust/Cargo, Charon, Aeneas, their unchanged
standard models, native exporter execution, JSON and the MPC backend remain
the stated trust boundaries.

## Proof organization

* `CopyReference.lean` and `CopyBridge.lean` cover the actual reverse copy loop
  and `memshift32` for every aligned, in-bounds public source position.
* `ColumnsReference.lean` and `ColumnsBridge.lean` cover the complete actual
  `xor_columns` loop for all words and public in-bounds offsets/distances,
  including overlapping ranges and every 32-bit rotation distance.
* `ArrayWindows.lean`, `ArrayHelpers.lean`, `RoundBody.lean` and
  `ExpansionLoop.lean` compose the real borrowing operations and prove all
  seven key-expansion iterations.
* `Initialization.lean` connects every input array to the bitplane layout.
  `FullSchedule.lean` composes initialization, expansion and the actual suffix
  proved in `../AesKeyScheduleFinishWork/`.
* `../AesKeyScheduleLeavesWork/` provides unchanged-helper equality, whole-word
  S-box and inverse-shift bridges. Its separate audit checks 44 endpoints;
  the finish package checks 28. The copy/column audit checks 26 endpoints.

`TlsMpc/Signal/AesKeySchedule.lean` is the fixed-control-flow implementation;
`AesKeyScheduleOps.lean` supplies word operations and `AesKeyInput.lean` packs
the secret input bytes and proves the final numeric lowering.
`PublicCheck.lean` additionally checks the schedule representation against
the existing byte-oriented AES expansion on 16 fixtures. Universal equivalence
to that separate byte-oriented expansion has not been proved.

Full AES block/CBC equivalence is still open. The actual round-key caller hits
unsupported mutable `Zip` borrow write-back, and the complete inverse-layout
wrapper hits hybrid-array initialization using `MaybeUninit`, raw slices and
`transmute_copy`. Those are computational boundaries and have not been removed
as metadata. See `../AesAddRoundKeyWork/` and `../AesInverseLayoutWork/`.

## Reproduce

```sh
python3 SignalReference/extract.py aes256_key_schedule --charon-only
python3 SignalReference/AesKeyScheduleWork/inspect_metadata.py
python3 SignalReference/AesKeyScheduleWork/check.py --packages-dir PATH
python3 SignalReference/AesKeyScheduleLeavesWork/check.py --packages-dir PATH
python3 SignalReference/AesKeyScheduleFinishWork/check.py --packages-dir PATH
python3 SignalReference/AesKeyScheduleWork/check_schedule.py --packages-dir PATH
python3 SignalReference/AesKeyScheduleWork/check_schedule_backend.py
```

The canonical package audit must already pass because these modules reuse its
accepted primitive proofs. `PATH` is the cache of dependencies at the exact
revisions in the pinned Aeneas Lean package. Backend compilation uses shared
MP-SPDZ paths and should run sequentially with other backend checks.
