# Actual generic Prost submessage source candidate

The original pinned `prost::encoding::message::merge` and `merge_loop` bodies
are extracted unchanged, including the actual FnMut closure, wire check order,
recursion check/decrement, parent remaining limit, and post-field overrun check.
The accepted scoped loop-pass translator generates these bodies reproducibly.
The FnItem-only candidate failed early-return loop translation; its local failed
outputs are preserved but unaccepted.

The same grounded typed projection from FnMutBorrowV1 is instantiated here.
Only explicit borrowed-triple trait type annotations are specialized. The actual
raw closure helper is moved unchanged to a namespace; a tagged operation exposes
raw order for standalone calls and the proved permutation for the trait field.
Inverse projection retains result, closure, message and buffer on all outcomes,
including fail/div. No arbitrary function coercion or assumed merge result.

Primitive aliases/adapters reuse actual accepted key/varint/wire/context bodies
and the scoped contiguous safe buffer content/forwarding representation. No
arbitrary segmented-buffer or allocator/unsafe-memory equivalence is claimed.
`Reference` proves exact actual closure projection, wire rejection before reads,
zero recursion rejection, exact end success and post-field parent-tail overrun
error with the current mutated message and suffix retained.

The actual source reads from the parent buffer: a child field can consume past
its declared child boundary before `DelimitedLengthExceeded` is detected. Native
checks include this case. Any later bounded streaming relation must preserve the
actual internal result first, then justify the owned-error functional observation;
it cannot assert equal internal error constructors/cursors after early rejection.

10,800 original/wrapper native comparisons cover all wires, duplicates, unknown
fields/groups, malformed strings, existing values, child lengths and parent tails.
They supplement the kernel facts; complete submessage scan/outer envelope and
streaming/compiler composition remain open. The std UTF8/content and diagnostic
static-push model boundaries inherited by the inner schema remain explicit.
