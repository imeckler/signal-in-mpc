# Group guards, stack operations and source recursion boundary

GroupKeyGuard derives schema opacity for every nested tag, including field numbers
1 through 5, and accepted non-end keys within the inner response depth bound.
Closing-key guard is exactly the native tag comparison against the stack top,
without imposing the non-end depth budget on closing. GroupRecognition proves
nested terminals install zero scalar/field schema masks.

GroupBudget proves depth-99 inner non-end rejection. GroupLimitSource executes
the actual unchanged source group/default path at recursion count 1: decode the
next non-end child key, descend to count 0, return RecursionLimitReached without
reading the child value, retaining its exact post-key suffix and source record.
The numeric depth/source-context induction itself remains an OPEN composition.

GroupStackLookup derives actual oblivious reads from bounded numeric indices.
GroupStackWrite derives exact selected-slot update and older-slot preservation.
GroupEndActive connects the closing guard to the last active slot and exact
source parent-tag equality, preserving mismatched-end rejection. GroupPush proves
actual terminal stack updates, independently of validity, rather than discarding
mutated rejected states. Slot/index bounds explicitly exclude modular aliasing.

These are group-composition primitives: full recursive source-group/streaming
agreement, source recursion-context/stack invariant and private child bounds at
group transitions, whole scan, headers/outer/HTTP/correlation/compiler remain OPEN.
No success-only response claim, new correctness axiom, runtime/backend change,
native execution or performance export. Inherited successful bounded content/
allocation, std UTF8 and static diagnostic-push boundaries remain explicit.
