# Actual XOR-assignment leaf and round-key boundary

The value-taking Rust core `BitXorAssign<u64> for u64` implementation has an
Aeneas-to-numeric-circuit equivalence proof for all two secret 64-bit operands.
This function is called transitively by pinned `aes 0.9.1` `add_round_key`.
`Proofs.xor_refines_artifact` connects its actual generated return value to the
exported circuit. The artifact uses 64 XOR operations and zero executed AND
operations. Four theorem endpoints and all 128 basis inputs are checked.

The **whole `add_round_key` loop is not proved**. Its source remains unchanged:

```rust
for (a, b) in state.iter_mut().zip(rkey) {
    *a ^= b;
}
```

Actual extraction of that loop, including the real shared-argument and
value-taking XOR-assignment helpers, exposes a mismatch in pinned Aeneas's
standard iterator model. `IteratorIterMut.next` returns a mutable borrow
write-back continuation as its third result component. Generic `Iterator.next`
expects only the pair `(Option T, iterator)`. The translated `Zip.next` and
`Iterator.zip` calls also require write-back components that their pinned
models do not provide. The generated Lean therefore fails type checking;
`check.py` deliberately reproduces this failure and records it separately.
No custom mutable `Zip` model or replacement Rust loop was introduced.

The extraction attempts are preserved under `Artifacts/`:

| Profile | Outcome |
| --- | --- |
| Base | Charon succeeds; Aeneas lacks the `Iterator.zip` dictionary slot. |
| IncludeXor | Includes both actual XOR-assignment bodies using full-MIR Rust core. Removing four unused `zip` dictionary slots, while retaining the actual regular `zip` call and its provenance, permits Aeneas emission. Lean rejects the mutable write-back signatures described above. |
| MonoZip | Includes actual `Zip` bodies and monomorphizes. Aeneas cannot translate `Option<(&mut u64, &u64)>`. |
| Mut | Partially monomorphizes mutable-reference uses, with required associated-type/ADT-clause flags. Aeneas reports duplicate builtin `zip` names and the missing dictionary slot. |

Only `Generated/XorAssign/` is an accepted proof reference after the independent
review and `check.py` succeed. `select_xor.py` retains actual function
declarations 6 and 121, their trait declaration, and two impl declarations,
without changing source, signatures, or bodies. Every discarded declaration
is recorded reversibly. Aeneas omits the now-unused shared-argument forwarding
wrapper; consequently the formal endpoint covers only the generated
value-taking implementation. No separate shared-wrapper refinement is claimed.

The retained trait/impl metadata mentions vtable type 45 and globals 6 and 7.
All three were already absent in the original Charon graph, and none is used
by the retained computation. This is explicit metadata, not an opaque
computational dependency. The independent selection review is at
`../AesKeyScheduleWork/xor-assign-selection-review.json`.

The accepted extraction pins remain Aeneas
`5b9dcf33dccdb1560ea7203ac57ea202476b6ed3`, Charon
`4ad295c1bf982b5533ce7d85f4ddc889ff3127f8`, Rust nightly 2026-08-18
(`8fa1c96cfd489e4c27654c144ae871ce2c4db6c6`), and Lean 4.31.0.
`check.py` verifies the official Rust source archive, the exact macro and
operator sources, the full-MIR sysroot artifacts, the unchanged official
Aeneas scalar models, package revisions, and theorem assumptions. The accepted
proof files have no custom axioms, incomplete proofs, or native-decision proofs.
Native serialization and the MPC backend remain unverified. No native
multi-party execution was performed for this artifact.

Reproduce the selected leaf and the recorded loop failure:

```sh
python3 SignalReference/AesAddRoundKeyWork/extract.py --variant IncludeXor --charon-only
python3 SignalReference/AesAddRoundKeyWork/inspect_metadata.py --variant IncludeXor
python3 SignalReference/AesAddRoundKeyWork/select_xor.py
python3 SignalReference/AesAddRoundKeyWork/check.py \
  --packages-dir /Users/izzy/repos/eco-theorem-combined/.lake/packages
```

This leaf does not establish whole AES, AES-CBC, or Signal send-path equivalence.
