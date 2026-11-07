# Reusable bridges for the actual AES256 key schedule

These proofs connect helpers from the reviewed
`AesKeyScheduleWork.Generated.Funs` extraction to existing proved root
operations. They import the unchanged generated implementation directly.

All theorem names below are in
`LibSignalReference.Proofs.AesKeyScheduleLeaves`.

| Import | Main usable results |
| --- | --- |
| `AesKeyScheduleLeavesWork.Equalities` | `sub_bytes_eq`, `sub_bytes_nots_eq`, `bitslice_eq`, `read_reordered_eq`, `delta_swap1_eq`, `delta_swap2_eq`, and forward/inverse ShiftRows equalities. All twelve function equalities are definitional and preserve complete `Result` behavior. |
| `AesKeyScheduleLeavesWork.SubBytes` | `restored_slice`: for any eight-word `Slice U64`, actual `sub_bytes` followed by actual `sub_bytes_nots` returns a list whose bitvectors equal `AesSbox.circuit AesKeySchedule.wordOps` on the input list. `restored_wordSlice` gives the fixed `Words` constructor form. |
| `AesKeyScheduleLeavesWork.InverseShift` | `inverse1_slice`, `inverse2_slice`, `inverse3_slice` target root `concrete.inv1`, `.inv2`, `.inv3`. Corresponding `_reference` theorems cover arbitrary `Words`; `_rejects_shape` and `_refines_artifact` preserve errors and reuse existing numeric circuit bridges. |
| `AesKeyScheduleLeavesWork.Nots` | `nots_slice` equals root `restoreNots concrete 0`. `sub_bytes_preserves_shape` and `nots_preserves_shape` return an actual successful output of length eight, for composing separate array-window borrows. |
| `AesKeyScheduleLeavesWork.Layout` | `bitslice_reference`, `read_reference`, `delta2_reference`, and `bitslice_refines_artifact` reuse the accepted layout implementation proofs. |

`restoredSubBytes` is precisely the two generated Rust calls in sequence; it
does not replace either implementation. The whole-word S-box theorem lifts the
existing implementation comparison through a bit-lane homomorphism, preserving
all 512 unrestricted secret input bits. Its `wordSboxOps` record is definitionally
equal to root `AesKeySchedule.wordOps`.

The inverse wrappers directly call forward ShiftRows 3, 2, and 1, respectively,
in the pinned Rust source. The proofs transfer the already-accepted operations
without assuming a representation invariant beyond their stated input shape.
The raw `sub_bytes` shape lemma follows from successful composition and the
second operation's actual eight-word assertion; no duplicate S-box network
proof is needed.

The reference remains libsignal `0.106.1` with locked `aes 0.9.1`, Aeneas
`5b9dcf33dccdb1560ea7203ac57ea202476b6ed3`, Charon
`4ad295c1bf982b5533ce7d85f4ddc889ff3127f8`, and Lean 4.31.0. The key-schedule
reference uses the reviewed metadata preprocessing recorded in
`../AesInverseLayoutWork/key-schedule-metadata-review.json`; all initial review
concerns there have been resolved. This extra extraction preprocessing remains
explicitly trusted, alongside faithful Charon/Aeneas translation and the pinned
standard models.

`check.py` replays that preprocessing, checks the unchanged generated files,
verifies official model archives and proof-package revisions, checks reused
canonical proof hashes, rebuilds the imported root operations and this package,
and audits all theorem assumptions. It records every workspace Lean dependency
and its hash in `proof-check.json`. The only allowed foundational axioms are
`propext`, `Classical.choice`, and `Quot.sound`.

```sh
python3 SignalReference/AesKeyScheduleLeavesWork/check.py \
  --packages-dir /Users/izzy/repos/eco-theorem-combined/.lake/packages
```

There are no new Rust extraction profiles, circuit implementations, runtime
artifacts, or backend tests in this package. Existing numeric bridges are
reused. These helper results support the separate full key-schedule composition
proof; they do not themselves establish that complete operation.
