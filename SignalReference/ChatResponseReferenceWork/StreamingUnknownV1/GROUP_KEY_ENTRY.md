# Actual nested non-fixed key entry

GroupKeyValidity derives actual Core validity from native key acceptance for
varint/length/start-group wire classes at positive depth <=98, with the key
strictly inside the private child. Native/schema/depth guards are derived, not
supplied as acceptance masks. All tags, including known field numbers, remain
schema-opaque inside the group.

GroupKeyStack proves exact stack preservation through arbitrary continuing key
prefixes and non-start terminals. GroupDepthStep proves exact native all-wire
terminal push/pop/no-change depth mutation, independently of validity, retaining
mutation on rejected states rather than erasing failed paths.

GroupKeyEntry composes these facts into one actual decoded key prefix: exact
native suffix and consumed bytes, unchanged response cache, derived validity,
mode/lexer/tag, zero scalar/field masks, depth transition and actual tag-stack
write, private remaining/public budget and state shapes. A start key installs
its actual native tag at the previous depth; other supported keys retain stack.

Initial numeric validity/cache/state bounds and the actual native key run remain
explicit composition inputs. Fixed/end key entry, native errors, source recursion
context/active-stack invariant, complete recursive group/private-child/whole scan,
headers/outer/HTTP/correlation/compiler remain OPEN. No complete response claim or
new correctness axiom; inherited bounded content/allocation, std UTF8 and static
DecodeError.push trust boundaries remain explicit. No runtime/backend/native or
performance-export changes.
