# Actual `MontgomeryPoint::to_edwards` translation blocker

The next actual-source refinement is **not proved**. The selected locked dalek
5.0.0 `to_edwards` body is byte-identical to the reviewed BAF fork
`95b5831c63ff1c5f6287bd3a77569412a9afdbfb`, but its full dependency stack must
still be translated and proved against our pinned implementation.

`extract.py ToEdwards` selects `crate::montgomery::*::to_edwards` in unchanged
pinned source. Charon succeeds with 62 function declarations. Pinned Aeneas
then exits 2 because its builtin `core::iter::range::Step` model lacks
`forward_overflowing`, reached through dalek `field.rs:60`. The exact logs,
commands, source hashes and declaration inventory are in `Artifacts/ToEdwards/`.
The reproducible LLBC and local build cache are excluded from Git.

No metadata deletion, LLBC rewrite, generated Lean edit, external model or
translator patch was applied. Even after repairing that translation issue,
Subtle and arithmetic/decompression dependencies, exact rejection semantics,
sign selection and circuit output agreement still need proofs. BAF's matching
entry body is useful provenance; it does not establish our dependency closure.
The accepted earlier decoder checkpoint remains unchanged.

```sh
python3 SignalReference/XEdDsaToEdwardsWork/extract.py ToEdwards
python3 SignalReference/XEdDsaToEdwardsWork/inspect.py
```

The command intentionally reports failure until translation is repaired. Its
entry inventory check rejects an empty selection (an exact Rust impl type name
is not the correct Charon pattern for this function).

`inspect.py` verifies the selected entry, source hashes, exact failure, and the
BAF source/proof files against the pinned review archive. `blocker.json` records
that provenance without importing the external proof or making a theorem claim.
