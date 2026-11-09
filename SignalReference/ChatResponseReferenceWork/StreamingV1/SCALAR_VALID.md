# Native successful scalar validity preservation

`ScalarValidity` proves actual Core validity for continuing scalar bytes strictly
before a child end and strict accepted terminal bytes, including a scalar ending
exactly at the child boundary at depth zero. Position liveness and strict tenth
byte overflow checks are derived; no machine-oracle axiom is used.

`ByteBudget` proves exact Core byte-budget consumption and seen/finished stability.
`ScalarPrefixValidity` composes the continuing-byte induction with explicit
remaining/budget bounds. `NativeScalarValidity` derives the complete varint span
from actual native success and proves actual Core validity through its complete
consumed field, with exact native suffix. No caller prefix/table or primitive
correctness premise is required.

Initial valid/seen/unfinished scalar state, depth zero, position zero, positive
child cursor and public byte-budget relations are induction-state/domain
conditions for the full scan to establish. They are not a complete parser
validity assumption. Budget/remaining are bounded by4096; native scalar success
must fit the declared child. Source varint error and child overrun rejection
remain in their independent all-input proofs, so the success theorem does not
replace the error observation or discard failed records.

Whole field data/control/valid joins, other field/group/private-EOF transitions,
HTTP/correlation/full compiler relation and inherited explicit source/std/model
boundaries remain open. Run `check_scalar_valid.py` for the isolated immutable
four-module combined kernel check.
