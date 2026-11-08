Actual pinned Prost uint32::merge reference candidate

uint32-proof-report.json covers the unchanged translated Rust scalar merge for
every contiguous Slice U8. It includes wire-type-first rejection without touching
the buffer, the accepted strict uint64 varint decoder and its exact error/suffix
behavior, modulo2^32 casting, preserving the old scalar on failure, and replacing
it on successful duplicates. The all-input theorem has no caller decoder premise.

No new external models or translator changes are introduced. Three accepted Buf
wrappers and nine accepted varint proof modules are replayed by exact namespace/
import substitutions, after checking the actual common decoder body is identical.
select_uint32_metadata.py records precisely seven unused Step dictionary edits,
with a pinned fingerprint, reversible paths and identical retained bodies. This
is the same explicit extraction/model trust boundary, with a new extraction that
still needs separate independent acceptance.

Reproduce:
  python3 SignalReference/ProtoParseWork/FieldReferenceWork/uint32-audit.py
This rebuilds13 modules and checks74 endpoint axiom closures, including8 new
scalar endpoints. Only propext, Classical.choice and Quot.sound are permitted.

The sibling bytes extraction is separate, unaccepted and not included in this
reference/model claim. Whole SignalMessage parsing, numeric table/scan invariants,
private MPC runtime and security remain outside this candidate.
