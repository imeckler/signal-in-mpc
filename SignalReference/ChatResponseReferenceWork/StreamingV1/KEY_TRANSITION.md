# Actual key transition component

`KeyTransition` proves Core terminal control transitions for all six protobuf
wire kinds: scalar, length, fixed32/fixed64, start/end group. It proves actual
stored tag and terminal value reset. Native successful key validation supplies
the exact kind/tag equalities used by those actual Core transitions; the native
key source is grounded by the prior terminal/key bridge.

The successful key branch is explicit. Invalid lexer/key paths are handled by
prior rejection/source-key components, but common key validity, known-field
wire guards, group limits, schema state and private-end bounds are not yet
composed into a complete streaming theorem. No response validity is assumed
or claimed. Existing source/std/content/diagnostic trust boundaries persist.

Run `check_key_transition.py` for a clean focused immutable check with inherited
receipt verification. No unrelated native tests are rerun.
