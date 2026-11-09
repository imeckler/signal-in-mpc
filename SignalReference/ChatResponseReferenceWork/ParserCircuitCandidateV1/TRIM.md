# Stack projection and Core trace checkpoint

Candidate only. `TrimStack.lean` erases exactly the high32 bits of each group
stack word. Every other state field is unchanged. Kernel proofs establish
idempotence, exact identity for narrow stacks, arbitrary-mask word selection,
stack write/lookup and state selection commutation, and finish commutation.

`trim_rejected_step` covers the crucial malformed-key case: a rejected original
state may retain high tag bits. The actual next step, followed by projection,
agrees with stepping the projected state and projecting again. Rejection and
all three event flags remain exact; no rejected intermediate tag is presumed
narrow. `trim_step` extends this to the valid-zero-or-narrow invariant.

`TrimProcess.lean` proves this equality for the unchanged actual Core.process,
including arbitrary private active/begin/end bytes, canonical-control guards,
fresh reset, finish, and event masking. `fresh_trimmed_trace_eq` lifts it to
all input lists: erasing the stack high half between every byte yields exactly
the original projected event trace. This retains every status/control/counter,
private bound and event flag on every byte, including malformed input and reset.

Remaining: actual byte codec pack/unpack/index bridge; Mux correlation/admission
trace composition; exported compact endpoint recurrence/compiler connection.
This is not yet the measured compact Mux stream equivalence theorem. Full actual
Rust schema/HTTP/correlation composition and its existing explicit model gaps
remain separate obligations. Shared Core/Mux/runtime sources are unchanged.
