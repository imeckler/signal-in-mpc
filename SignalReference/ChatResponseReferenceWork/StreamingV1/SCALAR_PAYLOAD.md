# Actual scalar payload component

`AnyVarint` eliminates supplied-prefix/table premises for native varint success
and error in key/scalar/length lanes. Success yields exact span, returned tail,
bounded count, actual Core decoded value and value/position resets. Every native
varint error rejects the complete Core fold/finish, including empty scalar and
length payloads; an empty key boundary is distinguished from an attempted field.

`ScalarPayload.actual_scalar_payload` composes the actual pinned uint64 and
uint32 mergers with that actual Core payload lexer for every input/outcome.
Native complete values, old-value preservation on error, error observations and
exact suffix are retained in scalarResult64/32, PrefixPost and ErrorPost. IDs
remain full uint64; the uint32 projection is proved low32 including overflow.

This is a payload component, not a full field/message refinement. It deliberately
does not assume the surrounding message valid: field bounds, inner-response
remaining length, optional-field initialization/duplicates and schema-state
updates must be joined in the scan invariant. Existing actual source dispatch
proofs retain those mutation/error details. Unknown/group/HTTP/private-length/
correlation/compiler composition and inherited explicit trust boundaries remain.

Run `check_scalar_payload.py` for a clean immutable two-module check reusing
verified ancestor objects; no unrelated native cases are rerun.
