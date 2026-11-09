# Mux stack-projection trace checkpoint

`mux_process_as_tail` is a definitional equality against the unchanged actual
Mux.process. The factored tail preserves its exact self-ID finish, private
slot eligibility, unique-match policy, non2xx abort policy, queue capacity,
consumption, reset, rows and event masks. No scheduling equivalence is asserted.

`trim_mux_tail`, `trim_mux_process` and `trim_mux_admit` prove stack projection
commutation for actual byte/admission operations. `fresh_mux_trimmed_trace_eq`
then proves the complete projected event trace equal when stack high halves are
erased after every operation, for arbitrary operation lists from initialization.
Admission operations produce a trace entry containing their complete projected
state and three zero event masks. Byte entries retain actual body/header masks.
All nonstack fields and low stack bits are exact, including malformed/rejected
paths, private controls, correlation, slot consumption, and reset. No success or
valid-message premise is used. Core reachability supplies valid-zero-or-narrow
safety and explicitly permits rejected high group tags.

Remaining: byte codec serialization/decoding and index carry, the measured
compact exported endpoint recurrence, and compiler-level stream composition.
This semantic recurrence proof alone does not promote the measured optimization.
No runtime/source/native job was changed or launched during the TLS hold.
