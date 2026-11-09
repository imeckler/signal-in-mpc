# Actual unknown length field continuation and malformed length errors

LengthScope/LengthHeaderReady join actual native length decoding with the full
post-header cache/child invariant: exact consumed header and suffix, private
remaining/budget, mode/skip, shape, lexer reset, depth, validity. Empty fields can
end exactly at the private child end; nonempty payloads remain strictly inside.
LengthResume composes arbitrary opaque payload bytes with the established skip
invariant, retaining the actual unchanged source record and exact final drop.
LengthIteration joins real generated key/default-field callback and parent-limit
loop continuation with this full numeric next-key/cache invariant.

LengthErrors preserves the exact malformed native length error, source record,
suffix and actual parent-loop error, and derives full numeric rejection. Keys
ending at/past the private boundary are rejected without borrowing parent suffix.

Entry is the existing live bounded ChildAtKey/cache relation and actual successful
unknown length key; fitting success additionally supplies the actual native length
run and private whole-field fit. These are field composition theorems, not a full
scan induction. Physical underflow callback/private overrun joins, groups, whole
scan/headers/outer/HTTP/correlation/compiler remain OPEN. The inherited executable
content/allocation, std UTF8 and static diagnostic-push boundaries remain explicit.
No runtime/backend edit, native benchmark or performance export.
