# SHA core constructor selection review

`check.py` independently replays and reverses the three exact unused
`ArraySize` implementation-metadata deletions. The ten original ordered roots,
five selected computational declarations, three types and two constants are
unchanged. The selected semantic call graph is closed and has no dependency
on the removed dictionaries. Eleven references in non-emitted diagnostic
declarations are retained and listed; this is not a closed whole-crate claim.

The review checks five registry archives against the pinned Cargo lockfile,
compares all 122 archived files to the vendor tree, compares all 87 Aeneas
standard-model files to the pinned archive, verifies the frozen proof-source
snapshot and checks eight transitive axiom reports through Lean.

Accepted scope is actual `Sha256VarCore::new` (including 28/32/invalid sizes),
and constructor-plus-already-accepted compact compression on sixteen words.
No `Digest`, update, finalization, byte-loading or block-buffer wrapper theorem
is established here. Metadata selection is an explicit trusted preprocessing
step rather than a mechanized proof. Acceptance is recorded separately in
`Sha256WrapperWork/acceptance.json`, preserving the author's frozen reports.

```sh
python3 SignalReference/Sha256InitialReview/check.py
```
