# Measured compact byte circuit: process/feed agreement

The candidate remains isolated; production Core/Mux/runtime are unchanged.
The exact existing measured candidate runByte is used throughout. Its4096-cap
profile remains40,529 executed AND gates versus65,825 baseline (38.4% saving),
AND depth275 for both. No new native benchmark or runtime promotion is included.

`CompactInput.lean` proves the exact586-byte encoded input expands to the full
982-byte trimMuxState plus all4 fresh private controls/data. This explicitly
handles the986-byte input versus985-byte output distinction. No missing input
byte is fabricated from an output event. Public inverse metadata is kernel
reduced with no native decision oracle.

`EncodedByteStep.lean` proves the actual compact numeric runByte equals the
compact original Mux.process event, under only reachable ABI shape and the
valid-zero-or-narrow parser stack invariant. The latter is proved for all
actual operation sequences and permits high scratch tags after rejection.
`CompiledEncodedByte.lean` proves every exported AIG bit agrees with that exact
original event for arbitrary symbolic inputs/assignments matching the encoding.
This uses the unchanged existing all-assignment compiler theorem.

`CompactCarry.lean` proves the next input is exactly the previous585-byte output's
first582 state bytes plus4 fresh controls, preserving all private state and
excluding the3 event bytes from feedback. `CompactFeed.lean` lifts this actual
feedback recurrence to equality of every output byte on every step for arbitrary
private active/begin/end/data lists. The theorem allows malformed keys, partial
varints, UTF8/header rejection, duplicate/unknown/group behavior, reset, private
bounds, correlation, queue consumption and non2xx application abort exactly as
Core/Mux implement them. It is not success-only. Arbitrary earlier actual Mux
process/admit prefixes establish the starting state, with no validity premise.
Fragment assembly remains the existing external endpoint; arbitrary controls
include the private fragment/message boundaries delivered by it.

Scope limits: this is circuit equivalence to existing Core/Mux, not the still
open complete actual Rust schema/HTTP/correlation refinement. Its std UTF8,
content/allocation and static diagnostic-push boundaries remain unchanged.
No exported compact admission circuit has been added/measured; interleaved
admission adaptation and native runtime integration remain separate before any
promotion. The actual Mux admit semantics/projection theorem is already proved.
Further counter/opaque-routing candidates must preserve this feed relation and
report both AND count and depth; the present stack compression has no depth win.
