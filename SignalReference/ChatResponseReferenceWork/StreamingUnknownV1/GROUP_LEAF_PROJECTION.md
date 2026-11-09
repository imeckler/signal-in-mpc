# Group leaf depth projection and native varint validity

GroupDepthProjection proves equality of the complete actual Core step/event when
depth is erased only in a proof-local copy, for scalar/length/opaque modes before
the private child closing byte. The real step retains its depth and stack; all
other fields, validity/error behavior, counters and event bits remain exact. No
success or validity premise is needed. It assumes only the explicit non-key mode,
kind-list shape and non-closing counter guard.

GroupVarintProjection derives this guard and mode at each byte of an arbitrary
continuing scalar/length prefix plus its next byte from strict remaining-input
bounds. It therefore proves the full feed equality without a per-step validity or
control-mask oracle. GroupScalarValidity and GroupLengthHeaderValidity compose
actual native decoder spans with that projection and previously checked flat
leaf proofs to preserve validity at arbitrary real group depth.

Strict field fit is required: an active group still needs its closing end tag.
Zero-length group fields do not silently close the response child. Native decode
runs, live bounded initial validity/counters and lexer/schema state are explicit
composition inputs, not an assumption that a response parser is correct.

Opaque span projection, complete recursive group/stack/source-context/private-child
relation and full scan/header/outer/HTTP/correlation/compiler composition remain
OPEN. Existing successful bounded content/allocation, std UTF8 and static
DecodeError.push boundaries remain explicit. No runtime/backend, native benchmark
or performance export changes.
