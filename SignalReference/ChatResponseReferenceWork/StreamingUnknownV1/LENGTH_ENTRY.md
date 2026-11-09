# Actual unknown length-delimited source and key entry

LengthSource executes the unchanged actual generated unknown-field branch and
actual Prost length-delimited skip for every native varint outcome. Native
termination is derived; malformed lengths preserve exact native errors/suffix,
physical payload underflow retains the post-length suffix, and success uses the
actual drop. The numeric length lexer agrees with successful terminal decoding
and rejects every native malformed-length outcome. No decoded result is assumed.

LengthKeyValidity/Entry/Ready derive numeric length-mode entry from actual native
and generated unknown key success and the live bounded child/cache invariant.
The consumed key, source suffix, unchanged field cache, zero kinds/scalar masks,
private remaining/budget counters and complete ChildReady are retained. No Core
validity mask or decoder-table entry is supplied as a premise.

This is a field-entry checkpoint: successful payload continuation, numeric physical
underflow/private-child overrun, complete callback/loop/scan, group semantics,
headers/outer schema/HTTP/correlation/compiler remain OPEN. Existing successful
bounded content/allocation, std UTF8 and static diagnostic-push boundaries remain
explicit. No runtime/backend changes, native run or performance export.
