# Actual group pop, malformed key and recursion-limit joins

GroupKeyError executes the real source group-body and loop exit for every native
key error, preserving its exact error and cursor while deriving Core rejection.
GroupLimitRejection joins actual depth99/source context1 to source child context0:
all non-end wire classes fail RecursionLimitReached before their value is read.
The exact native post-key suffix and full Core rejection are retained, including
keys crossing the private child. A matching end is separately allowed to close.

GroupPopReady executes the actual matching group body/loop successful return and
joins its decoded key prefix with exact cache/private state and active-stack pop.
For an enclosing group it constructs the restored parent U32 context and proves
the actual forward enter_recursion returns the current count. For the outermost
end it returns ordinary response ChildAtKey with context99, including exact
private child closure. Stale inactive stack data is retained. The active parent
slot is derived from the entire witnessed parent list, not supplied as a lookup
or acceptance oracle.

Inputs remain the live bounded witnessed group relation/cache, actual native key
runs and private end fit; nested successful pops must leave bytes for enclosing
groups. Fixed/length/mismatched/pop-overrun and recursive whole-group/full scan/
headers/outer/HTTP/correlation/compiler composition remain OPEN. No whole response
claim or new correctness axioms; inherited bounded content/allocation, std UTF8
and static diagnostic-push boundaries remain explicit. No runtime/backend/native
or performance-export changes.
