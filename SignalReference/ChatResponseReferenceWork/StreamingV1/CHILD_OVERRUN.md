# Declared-child overrun rejection

`LengthRejection` factors the actual Core remaining-input guard out of its real
step and proves rejection when that guard fails. It also proves a child boundary
inside a continuing varint forces rejection, even if later parent-buffer bytes
would terminate it.

`PrefixOverrun` lifts the boundary result through arbitrary continuing prefixes
and later tails, for key/scalar/length lanes. It then derives the prefix from
actual native varint success: any actual successful varint consuming past its
child limit causes complete-input Core rejection, without a prefix premise.

`ChildLengthOverrun` covers physically available length-delimited data extending
past its declared child limit, including a length prefix itself crossing the
limit. Counts use explicit positive remaining≤4096 and remaining≤physical input;
source varint success, physical payload bound and exact returned-length overrun
check are inputs from the real source field/submessage trace. No primitive
correctness or termination premise is assumed.

Native fields may consume/copy outer bytes before the parent reports an overrun;
other field errors can take precedence. Actual source error constructor/mutation/
suffix are retained by their existing references, not equated to Core's earlier
rejection position. Full scan still must derive the cursor/counter conditions,
handle zero-remaining attempted-field states via prior rejection, compose valid
field/event preservation, private EOF, remaining schema/HTTP/correlation/compiler
relations and inherited explicit trust boundaries.

Run `check_child_overrun.py` for an immutable isolated three-module combined check.
