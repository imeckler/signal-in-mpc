# All-input successful source key transition

`AnyKeySuccess` proves that every successful key at the actual generated schema
driver ABI supplies an exact input/tail span, bounded key count, and actual Core
stored tag, next wire-kind lane, zero accumulator and initial varint position.
No caller prefix decomposition, table result, or decoder-correctness premise is
required. Exhaustive lexer classification rules out malformed/truncated cases
using the actual native error bridge. Both noncanonical and canonical accepted
keys are included. `ListChoice` proves equal-length Core list-mask selection and
the terminal position reset without a machine oracle.

Together with the prior all-input source-key-error theorem this supplies both
branches at each attempted source key. The successful field/group transitions,
known-field wire and recursion guards, private-end bounds, complete scan relation
and HTTP/correlation/compiler endpoint composition remain open. This is not a
whole response parser theorem; inherited explicit trust boundaries persist.

Run `check_any_key_success.py` for an immutable combined two-module check using
verified ancestor objects, including the earlier rechecked key-circuit object.
