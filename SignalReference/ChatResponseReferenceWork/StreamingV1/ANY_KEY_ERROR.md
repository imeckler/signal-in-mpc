# All-input source key-error rejection

`LexerShape` proves an exhaustive input classification: accepted strict terminal
varint (including noncanonical forms), malformed tenth byte, or truncated
all-continuation prefix. Classification covers every byte list; it does not
assume a table row, decoder outcome or supplied prefix span.

`AnyKeyError` composes all three cases: for every nonempty input at a Core key
boundary, an actual native key decode Err implies actual Core rejection after
folding the whole input and finish. The theorem is also exposed at the actual
generated schema driver's key adapter. Native complete error/cursor observations
remain in the grounded key reference. Clean empty field boundaries are explicitly
excluded from this attempted-key theorem.

This closes the attempted-key-error branch needed by schema induction, not the
complete schema relation. Successful dispatcher fields/groups/private ends and
HTTP/correlation/compiler composition remain open. Inherited std/content/
allocation/static diagnostic push boundaries remain unchanged.

`check_any_key_error.py` verifies immutable ancestor sources/objects including the
separately rechecked accepted key-circuit dependency, and checks only the two new
modules with a distinct immutable combined log.
