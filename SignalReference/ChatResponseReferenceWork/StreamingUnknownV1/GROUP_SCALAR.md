# Actual group-loop varint iteration

GroupScalarStack preserves every actual stored slot, including inactive data,
through the native scalar span. GroupScalarComplete joins actual native decoding
with derived validity, exact consumed prefix/suffix, unchanged known-field cache,
mode/lexer reset, depth/stack and private remaining/inner state at real group depth.

GroupLeafBoundary assembles separately proved ordinary-field facts into the
explicit recursive active-stack/source-context relation. GroupScalarIteration
uses this helper to execute the actual unchanged Prost group-loop body: real key,
constructed checked U32 child context, actual enter_recursion and skip_varint,
then actual body continuation. The numeric key/field spans compose into the exact
same native suffix, unchanged cache and complete GroupLoopReady relation. Tag
numbers coinciding with response fields remain ignored inside the group.

Entry is the witnessed bounded GroupLoopReady/cache relation, source context,
actual native key and value runs, depth<=98 and strict whole-field private fit.
The latter leaves bytes for the required closing group tag. Native run termination
and all-outcome classification are not claimed by this successful iteration alone;
error/max-depth/fixed/length/pop joins and recursive whole-group/full scan/header/
outer/HTTP/correlation/compiler composition remain OPEN. This is no replacement
success-only parser or full response validity assumption. Inherited bounded
content/allocation, std UTF8 and static diagnostic-push boundaries stay explicit.
No runtime/backend/native/performance-export changes.
