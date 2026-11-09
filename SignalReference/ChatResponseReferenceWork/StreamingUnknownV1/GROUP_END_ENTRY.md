# Actual matching end-key transition and mismatched-end rejection

GroupEndTerminalValidity handles the response-closing byte explicitly: a matching
outermost group end pops depth1 to0 and preserves validity, including an exact
private child end. GroupEndKeyValidity derives this terminal and all continuing
prefix facts from actual native decode_key, actual active parent slot and bounded
input counters, rather than supplying a precomputed decoder row or guard mask.

GroupEndKeyEntry composes the exact actual native prefix/suffix with unchanged
known cache, validity, mode/lexer/tag and zero schema masks, pop-depth, unchanged
stack (including stale inactive slots), budget/remaining and exact inner closure.
Exact child closure is permitted only when it closes the outermost group; nested
closes must leave bytes for their enclosing group.

GroupKeyRejection preserves the real terminal step and proves rejection from its
actual bad key guard. GroupEndMismatch derives full-input rejection for every
actual mismatched end key: exact native key span, active stack/parent lookup and
private bounds are joined, including keys that physically cross the child. Initial
validity/acceptance is not assumed for this rejection theorem.

A witnessed active parent slot, actual native key run and explicit numeric state/
capacity bounds remain composition inputs. Initial/fixed/error group key joins,
recursive source context/stack/private-child group relation, whole scan/headers/
outer/HTTP/correlation/compiler remain OPEN. No full actual response claim. The
inherited successful bounded content/allocation, std UTF8 and static diagnostic
push boundaries remain explicit. No runtime/backend/native/performance changes.
