# Actual known-field wire guards

`WireGuard` defines typed executable projections of the actual Core key guard.
Its rejection theorem factors that clause out of the actual `step` computation,
retaining all common-key/recursion/input guards; it is not a replacement parser
or an assumed callback.

`KnownWire` proves the exact guard for all six native wire kinds at scalar and
byte/string/header/submessage sites. It also proves nested unknown groups never
acquire schema recognition. `WrongWireRejection` composes actual native key
success/span/value, bounded prefix context and sticky rejection: every known
outer or bounded inner field with wrong wire kind rejects the entire actual
Core fold and finish, without supplied prefix/table/new-tag premises.

Native source UnexpectedWireType constructor, diagnostics, initialized optional
fields and suffix remain in the existing actual field-dispatcher references.
These theorems establish Core rejection, not equality of error-time internal
records or a new diagnostic projection. Native key/payload cursor behavior is
preserved by the prior grounded references.

The bounded inner domain still explicitly supplies child-cursor/counter/depth
relations for the full scan invariant to derive. Correct-wire field effects,
unknown/group total streaming agreement, private EOF, HTTP/correlation/compiler
composition and inherited explicit trust boundaries remain open.

Run `check_wrong_wire.py` for an immutable isolated three-module combined check.
