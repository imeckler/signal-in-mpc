# Actual mutable-Zip extraction boundary

No usable extraction route was found in five targeted variants. The actual
`aes 0.9.1` `add_round_key` loop is unchanged, and this directory contains only
diagnostics. It adds no accepted reference, circuit proof, computational model,
toolchain patch or backend result. The previously proved value-taking XOR leaf
and the complete key-schedule proof remain valid separate results.

The source target is `src/soft/fixslice64.rs:1362` in the locked AES dependency
of libsignal `0.106.1`:

```rust
fn add_round_key(state: &mut State, rkey: &[u64]) {
    debug_assert_eq!(rkey.len(), 8);
    for (a, b) in state.iter_mut().zip(rkey) {
        *a ^= b;
    }
}
```

`State` has eight words. The extracted assertion and the original loop are
retained. No replacement Rust harness is used: every Charon invocation starts
from this actual function in the locked dependency.

The pinned stack is Charon `4ad295c1bf982b5533ce7d85f4ddc889ff3127f8`, Aeneas
`5b9dcf33dccdb1560ea7203ac57ea202476b6ed3`, Rust nightly 2026-08-18 and Lean
4.31.0. The existing full-MIR sysroot is read without changes.

| Reproduction | Result |
| --- | --- |
| `python3 SignalReference/AesZipInvestigation/reproduce.py` | Replays the prior reviewed removal of four unused `zip` dictionary slots, leaving every computational declaration unchanged. Aeneas emits the complete actual loop; Lean rejects its mutable iterator signatures. Also reproduces the minimal official-model type mismatch. |
| `python3 SignalReference/AesZipInvestigation/extract.py MutAll` | `--monomorphize-mut=all` preserves lifetime information; Charon succeeds. Aeneas rejects name collisions between generic and specialized `Zip`, `Option`, and iterator methods, then the missing `zip` dictionary slot. |
| `python3 SignalReference/AesZipInvestigation/extract.py MutAllZip` | Includes actual Zip bodies with partial monomorphization of types and functions. Charon panics during trait substitution. |
| `python3 SignalReference/AesZipInvestigation/extract.py MutExceptZip` | Includes actual Zip bodies with `--monomorphize-mut=except-types`, `--remove-adt-clauses`, `--lift-associated-types=*`. Same Charon panic; backtrace retained. |
| `python3 SignalReference/AesZipInvestigation/extract.py MutExceptConstructor` | Includes only the actual `Iterator::zip` constructor, with the latter partial mode. Charon succeeds; Aeneas still rejects specialized builtin-name collisions and the missing dictionary slot. |
| `python3 SignalReference/AesZipInvestigation/extract.py MutExceptNext` | Narrows actual-body inclusion to `--include=core::iter::adapters::zip::*::next`. This suffices to reproduce the Charon panic. No replacement source or custom model is involved. |

All exact commands, pins, inventories and logs are under `Artifacts/<variant>/`.
`Generated/Baseline/Funs.lean` is deliberately rejected generated code; it must
not be imported into an accepted proof package. The original full-monomorphized
candidate was also rerun with `-print-error-emitters -abort-on-error`; its
diagnostic is in `Artifacts/MonoDiagnostic/`.

The model mismatch has three concrete parts. In the pinned official Lean
library, `Aeneas/Std/Core/Iter.lean:79` requires `Iterator.next` to return
`Result (Option Item × Iterator)`. In `Aeneas/Std/SliceIter.lean:38`, mutable
slice iteration returns a third component:

```text
IterMut T → Result (Option T × IterMut T × (IterMut T → Option T → IterMut T))
```

The actual generated iterator implementation cannot place that function in
the generic two-component field. The actual loop also expects a write-back
continuation from `Zip.next`, whereas its model at `Core/Iter.lean:527` returns
only a pair. Finally, the caller expects `Iterator.zip` to return the adapter
and a continuation restoring its moved mutable iterator; the model at
`Core/Iter.lean:603` returns only the adapter. These continuations carry updated
secret words back into the original state. Removing an unused dictionary slot
cannot supply them. `ModelSignatureMismatch.lean` isolates the first mismatch
using only official model constants, without defining a replacement model.

The partial-monomorphization failure is independently actionable in Charon.
Its `src/options.rs:74` explicitly describes this option as preserving mutable
reference shape across generic instantiations. The narrowed `MutExceptNext`
profile reaches `MutabilityShapeBuilder.compute_shape`; its trait-type
constraint substitution at
`src/transform/normalize/partial_monomorphization.rs:109` invokes
`substitute_explicits` without a `Self` reference. The backtrace reaches
`src/ast/type_level/substitute.rs:117`, where `visit_self_clause` requires that
reference and panics. Both source files were checked against the pinned Charon
source archive. Including only the constructor does not reproduce this panic,
which narrows the relevant actual call graph to Zip's next-method bodies.

Full monomorphization is a separate failure. The actual LLBC contains erased
mutable and shared regions in `Option<(&mut u64, &u64)>`. The pinned executable
reports `llbc/TypesAnalysis.ml:229`. A cached source snapshot from commit
`7161abf2b8a830d7534f007f2b82e7931e66b921` shows rejection of an erased mutable
region at the corresponding location, consistent with the graph and stack.
This source explanation is an inference from that adjacent revision; exact
OCaml source retrieval for the pinned commit failed because external fetching
was unavailable. The error location itself comes from the pinned executable.
The exact official Lean model sources were available and archive-verified.

Two possible implementation directions remain explicit, unproved options:

- Repair Charon's `Self`-aware constraint substitution, then handle specialized
  mutable iterator types and methods in Aeneas's builtin registration. The
  observed name collisions are at `extract/ExtractBase.ml:269/303`; successful
  handling could expose further translation obligations.
- Add mutable-iterator and mutable/shared-Zip models that preserve both the
  per-element and whole-iterator write-back continuations, with exact terminal
  behavior. Any such extension would require a stated new trust decision or
  equivalence to the selected actual Rust bodies before it could close the
  circuit-versus-translated-implementation claim. It was not implemented here.

The newer cached September stack still has the same generic pair-valued
iterator models. Its `-filter-trait-methods` option addresses unused dictionary
fields, not these missing computational continuations; it was inspected but
was not substituted for the accepted stack.

`report.py` verifies source/archive provenance and diagnostic status, then
writes `report.json` with all artifact and source hashes. It does not convert
these expected failures into accepted proof results.
