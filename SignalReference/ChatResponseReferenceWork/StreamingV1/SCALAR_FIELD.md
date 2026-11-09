# Actual generated scalar field composition

`ScalarDispatch` composes the actual generated response ID/status field dispatcher
with the actual varint-backed primitive mergers, for arbitrary existing/absent
fields and every native outcome. The executable result retains None→Some(default)
initialization before error, duplicate replacement, full error constructor, exact
suffix, diagnostic stack push order and its fail/div effects. No error record is
relabeled as successful. The inherited static-push extraction boundary persists.

`IdPresence` proves actual Core ID terminal assignment sets presence even for
ID zero, using the same bounded successful span as its full64 value update.
`ScalarFieldRefinement` joins these with the numeric Core: on every input/outcome
the source result is exact; native varint errors force Core fold/finish rejection;
a successful bounded child field updates actual full64 ID+presence or exact
low32 status. Absent and duplicate fields are included.

The source success expression is unconditional, while the numeric successful
update explicitly requires returned suffix≥input−remaining. Full scan must derive
this child cursor condition and handle child overruns separately; it must also
prove preservation of the rest of the numeric message-state invariant. Therefore
these are scalar-field components, not a complete message refinement, not
success-only replacement for source error behavior, and not a full internal
error-time record equivalence.

Remaining correct-wire byte/string/header/unknown/group/private-end/HTTP/
correlation/source compiler composition and inherited explicit trust boundaries
remain open. `check_scalar_field.py` records a clean immutable three-module check.
