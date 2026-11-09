# Actual opaque/body transition component

`OpaqueBody` proves actual Core opaque-mode transition and exact skip decrement
for arbitrary bytes. Body data is emitted under exactly actual next-valid.
`OpaquePrefix` proves every proper prefix stays opaque with exact remaining count,
exact completion returns to key mode/zero count, and truncated actual input
rejects at EOF. Counts are bounded below2^64; no parser-validity premise is used.

`LengthBody` proves field-kind preservation through continuing length bytes and
actual body length/presence/reset, including empty bodies and duplicates. Zero
length returns immediately to key mode; nonzero length installs the exact skip
counter and enters opaque mode. Reset is visible under actual next-valid.

This component does not yet prove the valid mask stays255 through a valid body,
nor connect emitted bytes to the actual Bytes copy or optional source dispatcher.
Those require the source child-bound/message-state invariant. Source Bytes
allocation/content/copy/error semantics already have their separate reference.
String/headers/unknown/groups, private actual EOF/source agreement, HTTP/correlation
and complete compiler composition remain open. Inactive padding has its separate
proved process/compiler component; it is not used to supply missing payload bytes.
Inherited explicit std/content/allocation/static diagnostic push boundaries persist.

`check_opaque_body.py` checks these three new modules with immutable log, clean
aggregate exit and inherited source/object hash validation.
