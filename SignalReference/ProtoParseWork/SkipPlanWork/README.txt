Conditional numeric parser-plan bridge

This work refines the existing TlsMpc.Signal.ProtoParse.plan/applyPlan operations;
it does not replace the Rust reference with a circuit-shaped definition.

Fixed.lean proves numeric masks and cursors for fixed32/fixed64, varint and
length-delimited fields inside groups, bounded fixed/length arithmetic and
recursion-limit rejection. Reference.lean connects those decisions to the
accepted actual skip_field functions, including errors and exact remaining slices.

Group.lean proves start/end masks, depth/cursor changes, exact selected stack
writes and unchanged top-level fields for group contents. Stack.lean proves
oblivious lookup equals ordinary indexing under an explicit no-alias bound.
GroupReference.lean connects closing-tag decisions to actual Rust group-body
success/error using numeric key correspondence and the current stack entry.
Closing a group at depth100 is covered; entering another child is rejected.

Theorems explicitly assume decoded key/payload correspondence, slice/cursor
length correspondence and valid stack/state invariants where needed. Establishing
those premises for the whole table lookup/scan remains incomplete. Top-level
unknown/known field behavior, duplicate-field handling and the final Signal
message acceptance conditions are not covered by these theorems yet.

KeyCircuit.lean is an exact namespace/import replay of the accepted key proof,
recorded in key-replay.json. This avoids generated global discriminant-name
collisions when importing the actual skip translation. No model, generated Rust
function, translator source or accepted candidate dependency is modified.

Reproduce the full rebuild and transitive axiom audit:
  python3 SignalReference/ProtoParseWork/SkipPlanWork/audit.py

The scope is conditional numeric agreement. There is no complete numeric AIG
artifact/whole-parser refinement, totality, native execution or security claim.
