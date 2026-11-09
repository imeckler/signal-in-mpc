# Prefix metadata and scalar recognition

`VarintContext` proves actual Core continuing-byte metadata preservation directly
from its computation. `PrefixContext` lifts this to arbitrary continuing prefixes:
source tag, scalar-recognition flag and group depth are preserved; inside a
response the explicit ≤4096 remaining bound prevents premature close and the
counter decrements exactly. At the outer envelope inner stays zero. These lemmas
apply to key and length prefixes as well as scalar payloads, without a schema
validity assumption.

`ScalarRecognition` proves actual Core key-terminal recognition matches native
dispatcher tags: outer enum1 and inner ID1/status2. It takes the new-tag projection
proved by the native key bridge; the scan invariant must join that projection,
prefix context, known-field wire guards and native dispatch.

Full schema/unknown/group/string/bytes/private-end/HTTP/correlation/compiler
composition remains open. Source/std/content/allocation/static diagnostic push
trust boundaries remain inherited. `check_prefix_context.py` records a clean
immutable three-module combined check with verified ancestors.
