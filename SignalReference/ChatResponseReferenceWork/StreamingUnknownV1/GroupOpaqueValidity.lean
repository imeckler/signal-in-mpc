import ChatResponseReferenceWork.StreamingUnknownV1.GroupOpaqueProjection
import ChatResponseReferenceWork.StreamingUnknownV1.OpaquePrefixValidity
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1

/-- Arbitrary unknown opaque payload bytes preserve validity inside a group,
retaining the actual depth. The payload must leave space for its group end;
private padding cannot be used to satisfy that strict bound. -/
theorem group_opaque_prefix_valid (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (bytes : List (BitVec 8)) (count budget remaining : Nat)
    (budgetBound : budget ≤ 4096) (remainingBound : remaining ≤ 4096)
    (budgetEnough : bytes.length ≤ budget) (payloadEnough : bytes.length ≤ count) (strictFit : count < remaining)
    (modes : state.modes = lane 3) (kinds : state.kinds = [0,0,0,0])
    (valid : state.valid = 255) (seen : state.seen = 255) (finished : state.finished = 0)
    (inner : state.inner = 255) (skip : state.skip = BitVec.ofNat 64 count)
    (budgetCounter : state.budget = BitVec.ofNat 64 budget) (childCounter : state.responseRemaining = BitVec.ofNat 64 remaining) :
    (feed state bytes).valid = 255 := by
  have kindShape : state.kinds.length = 4 := by rw [kinds]; rfl
  have projection := group_opaque_depth_projection state bytes count remaining remainingBound payloadEnough strictFit modes kindShape inner skip childCounter
  have flat := unknown_opaque_payload_prefix_valid (eraseGroupDepth state) bytes count budget remaining budgetBound remainingBound
    budgetEnough payloadEnough (by omega) modes kinds valid seen finished inner rfl skip budgetCounter childCounter
  rw [projection] at flat
  exact flat

#print axioms group_opaque_prefix_valid
end ChatResponseReference.StreamingUnknownV1
