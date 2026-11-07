# Isolated extraction-toolchain investigation

The accepted reference remains the August 27 Aeneas/Charon toolchain in
`pins.json`. `candidate-pins.json` and `candidate_tools.py` record an isolated
September 30 candidate: Aeneas `0855ce1b8ed3958512b6c19de6bf3035b7acb552`, its
bundled Charon `e435e5f341863a49a7e85d2fee9988bc0c687c82`, and Rust nightly
2026-09-17. Both Aeneas releases use Lean 4.31.0. Official binary, backend-cache
and Rust-component archive hashes are recorded; no source patches were made.
No candidate output is accepted as a proved implementation reference.

All attempts use the original libsignal commit and Cargo-locked dependencies.
The inventories, commands and failure status are under
`Extraction/Candidates/2026-09-30/`.

| Selected operation | Actual result with the candidate |
| --- | --- |
| Compact SHA-256 compression | Charon completes, but Aeneas lacks the `Step::forward_overflowing` trait field used by the Rust range loop. Filtering unused trait methods does not repair the trait declaration. |
| Compact SHA-256 with monomorphized bodies | Charon exposes 12 structured bodies and one intrinsic. Aeneas's array-default preprocessing then looks up missing trait-declaration metadata and fails. Excluding the array trait moves the same problem to slice indexing; it does not produce an accepted reference. |
| Full symmetric ratchet key derivation | Charon still encounters generic associated types in `hybrid-array`; the reference is incomplete. |
| Fixed-width ServiceId decoding | Aeneas fails in actual Rust `Result::ok` with `There should be no bottoms in the value`. The additional Charon drop-resugaring flags produce the same failure. |

These attempts distinguish tool limitations from cryptographic proof work. They
do not justify replacing a dependency body with an opaque primitive. Accepted
scalar-round, identifier and tag proofs continue to use the original toolchain.

The padding helper subsequently built an official full-MIR Rust sysroot with
the matching Miri nightly. This lets Aeneas extract the actual slice iterator's
`any` loop without Rust's precompiled MIR inlining it into raw-pointer accesses.
Its provenance and unpadding work are isolated in `PaddingWork/Unpad/`.

`build_full_mir_std.py` extends that approach to a separate sysroot including
`std`, using the same official Rust/Miri artifacts and unchanged source. Its
source and output hashes are in `Extraction/full-mir-std-sysroot.json`. The
`service_id_decode_full_mir` profile still fails in actual `Result::ok` at
`core/src/result.rs:718`; a less-optimized sysroot does not fix that translator
problem. The `sha256_compact_full_mir_mono` attempt selects actual range
iterator bodies, reaching five structured functions, but still fails in
Aeneas's `TypesUtils.as_ident` handling of monomorphized names. Neither attempt
is accepted as a refinement reference. These profiles use separate disposable
Cargo caches because artifacts built against different sysroots are incompatible.

`MetadataWork/normalize_names.py` isolates the monomorphized-name crash further.
It changes only two declaration-name slots, replacing a trailing instantiated
name item with a unique identifier; restoring those slots makes the entire
JSON equal to the original. Rust bodies, signatures, constants, IDs and control
flow remain unchanged. This unproved naming step is an additional trusted
extraction candidate, not part of the accepted reference pipeline.

For `sha256_compact_full_mir_mono`, that candidate lets Aeneas translate the
actual five-function compression/iteration graph, but leaves
`Step::forward_unchecked` as an external template. The complete profile selects
the actual unchecked-add/UB-precondition path too; it then fails when Aeneas
checks the real `fmt::Arguments::from_str` argument in that guard. Neither output
is accepted as complete SHA equivalence. Exact changes, hashes, template lists
and logs are in `MetadataWork/Artifacts/ShaCompactNames/` and
`MetadataWork/Artifacts/ShaCompactComplete/`.

A separately reviewed generic-profile workaround has now completed its operation
proof. `MetadataWork/trim_step_metadata.py` removes only the two unused opaque
Step fields and their declarations/order entries. An independent review checked
the full retained semantic graph, including globals and function pointers, and
the pinned official Aeneas range model. Repeated Charon extraction changes only
the order of diagnostic `short_names`; the pinned fingerprint sorts that map
for comparison while preserving the actual LLBC untouched elsewhere. The
accepted `sha256_compact_reviewed` profile and its exact diff are recorded in
`Extraction/sha256_compact_reviewed.json` and
`Extraction/sha256-compact-metadata/review.json`. This extra trusted filtering
step is not mechanized. Unlike the unsuccessful monomorphized candidates above,
its generated reference has no external templates and its complete selected
compression operation is related to a numeric MPC circuit. Digest/HMAC/HKDF
composition is still separate.
