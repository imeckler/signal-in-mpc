# Actual inner-group length-delimited loop continuation

GroupLengthStack proves actual complete length-header stack preservation.
GroupLengthHeaderComplete joins actual native header decoding, private counters,
cache and full control/validity at retained group depth. Empty payloads are covered
without allowing their header to close an unfinished group. No primitive/decoder
row/next-state/acceptance oracle is supplied.

GroupLengthComplete joins that header with arbitrary opaque payload bytes and
exact native drop, retaining actual depth, the whole stack including inactive
slots, cache, lexer/mode, validity and private remaining/inner state.
GroupLengthIteration executes the actual unchanged Prost group body: real key,
constructed checked child context, enter_recursion, native length decode/physical
skip and body continuation, composing the complete witnessed recursive frame.
Physical payload fit is derived from strict private whole-field fit.

Entry remains the bounded witnessed inner frame/cache, depth<=98, actual native
key/header runs and strict whole-field private fit. Native termination/all-outcome
classification, length errors/boundaries and recursive whole-group/full scan/
headers/outer/HTTP/correlation/compiler remain OPEN. Unknown group payloads are
arbitrary bytes; they do not acquire known response-string UTF8 restrictions.
Inherited bounded content/allocation, std UTF8 and static diagnostic-push boundaries
stay explicit. No runtime/backend/native/performance-export changes.
