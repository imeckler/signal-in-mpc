# Complete copied-body cached-data transition

`ResponseData` is a proof-only projection of actual Core cached response fields,
not a replacement for the final source observation. It excludes control/scratch,
validity and body/header byte events. Actual source full contents/errors remain
in the existing reference and body-dispatch theorems.

`OpaqueData` proves continuing varint prefixes and proper/exact opaque payload
prefixes preserve those cached fields. `NativeBodyData` joins native success and
actual Bytes copying with the Core's entire consumed field: exact input/returned
suffix partition, replacement body length/presence, preservation of all other
cached response data, final key mode and zero skip. Empty and duplicate bodies
and arbitrary byte values are included. `actual_body_field_data_success` exposes
the actual generated dispatcher result and that complete cached-data relation
together, without prefix/table premises or a parser-validity assumption.

The final parser observation is not weakened to this cache projection. Validity
preservation, complete emitted body-byte equality, child-limit overrun/remaining
relations, other fields/groups/private EOF, HTTP/correlation/full compiler
composition and inherited explicit trust boundaries remain open. Prior proofs
retain every source body error/default/diagnostic/suffix effect and establish
Core malformed-prefix/physical-underflow rejection.

Run `check_body_data.py` for an isolated immutable combined three-module check
with verified ancestors; no unrelated native cases are rerun.
