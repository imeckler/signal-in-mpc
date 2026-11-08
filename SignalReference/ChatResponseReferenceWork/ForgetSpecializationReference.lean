-- Mechanical exact declaration replay; see forget-specialization-audit.json.
import Aeneas
open Aeneas Aeneas.Std Result
namespace ActualChatResponseStringForgetSpecialized
def encoding.string.merge.DropGuard := alloc.vec.Vec U8
def prost.reference_forget_drop_guard
  (t : encoding.string.merge.DropGuard) :
  Result encoding.string.merge.DropGuard
  := do
  ok t

theorem forget_preserves_borrow (v : encoding.string.merge.DropGuard) :
  prost.reference_forget_drop_guard v = .ok v := rfl
#print axioms forget_preserves_borrow
end ActualChatResponseStringForgetSpecialized
