import CtrReferenceV1Work.CheckedRemainingV1Work.Generated.Types
import CtrReferenceV1Work.StateRemainingReference
import CtrReferenceV1Work.ReadBufferV1Work.CursorReference
namespace ActualCheckedCtr16
open Aeneas Aeneas.Std
open LibSignalReference.Candidate
-- DEF adapters retain the actual functional computations; no crypto result axiom.
def Core.remaining_blocks (self : Core) : Result (Option Usize) := do
 let remaining ← CtrStateV1.remaining (CtrState.zeroNonce self.counter)
 match remaining with
 | .Some value => .ok (some value)
 | .None => .ok none

def ReadBuffer.remaining (self : ReadBuffer) : Result Usize :=
 ActualReadBuffer16.ReadBuffer.remaining ⟨self.buffer⟩
end ActualCheckedCtr16

open Aeneas Aeneas.Std
-- Narrow trusted Std binding of pinned uint_macros.rs quotient/remainder/add body.
-- Division/remainder-by-zero and checked-add failure are retained.
def core.num.Usize.div_ceil (value divisor : Usize) : Result Usize := do
 let d ← UScalar.div value divisor
 let r ← UScalar.rem value divisor
 if r > 0#usize then UScalar.add d 1#usize else .ok d
