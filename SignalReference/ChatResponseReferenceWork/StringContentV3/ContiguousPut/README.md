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

GeneratedReference.put_reference now kernel-checks the generated guarded copier
without computational edits. It gives exact append and remaining slice for every
input, old vector and Usize limit in the executable model, including its capacity
failure branch. GeneratedOneStep/FunsExternal.lean is an explicit scoped model:
accepted bounded Vec allocation/content, safe contiguous slice operations, and
Take content/loan restoration. Mutable inner forwarding uses the separately
proved actual TypedLoanProjection; Take's raw loan model is still a stated ABI
boundary. This does not establish arbitrary Buf or unsafe-memory correctness.
check_generated.py builds the affected dependency closure in a separate output
folder and records source/object hashes and foundational-only theorem axioms.
Historical loop-audit.json remains unchanged as the earlier checkpoint receipt.
