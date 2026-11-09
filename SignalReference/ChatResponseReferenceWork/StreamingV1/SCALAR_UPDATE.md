# Bounded scalar state updates

`ScalarContext` and `ScalarPrefixContext` prove actual Core scalar-prefix tag,
recognition flag and inner-response state preservation with exact counter
decrement. The input domain is explicit: remaining ≤4096, actual prefix length
strictly below remaining. No response validity is assumed.

`VarintSpan` derives the entire terminal span from actual native success for
every input, without caller prefix/table premises. `ScalarUpdate` joins that
span to the real bounded child-cursor condition:

* remaining ≤ actual native input length;
* actual returned suffix length ≥ input length − remaining.

Those checks derive that the terminal byte lies inside the response. The actual
Core's ID update then equals the full native uint64 value, and its status update
equals the native uint32 cast, including high-bit truncation. This closes scalar
data mutation at a bounded response-field site, using the prior grounded actual
uint64/u32 merger bridge. The source has not been changed.

The full scan invariant must still establish these child-counter/cursor checks
and source-field recognition from submessage execution, compose optional-field
initialization/duplicates and unknown/group/string/bytes cases, and connect
private end, HTTP validation/correlation/compiler endpoints. Explicit inherited
std/content/allocation/static diagnostic push boundaries remain unchanged.

`check_scalar_update.py` checks only these four new modules in an isolated output
with immutable combined log and verified ancestors.
