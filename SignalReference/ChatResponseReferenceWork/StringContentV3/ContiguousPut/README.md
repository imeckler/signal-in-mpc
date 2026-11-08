This candidate lowers the actual pinned Vec.put loop only on the explicit
contiguous Take content domain. LoopLowering refers to the already extracted
actual source body/loop, preserves first-body errors/divergence, and retains the
exact successful body suffix. CanonicalTake derives exhaustion for every slice
and Usize limit; primitive termination is not a premise.

The original source-body replay remains separate. The guarded one-body Rust
variant changes while to if and checks exhaustion after a successful body.
Original actual Vec.put, exact-body replay, and guarded variant agree on 7,020
native vector/suffix outcomes, including empty input, old values and usize::MAX
limits. check_loop.py rechecks source/proofs and records hashes in loop-audit.json.

The guarded variant extracts and translates in isolation; the original concrete
loop fails Aeneas nested-borrow abstraction, and the fully generic specialized
loop fails at an ended-region expansion after chunk/advance. Neither failed
extraction is accepted as a source proof. The loop theorem supplies the explicit
control-lowering condition; actual Std Take/borrowed trait models and generated
copier kernel check remain required before String/owned-decoder composition.
No full String/response refinement or universal Buf behavior is claimed.
