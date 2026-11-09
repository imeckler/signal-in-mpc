import ChatResponseReferenceWork.StreamingUnknownV1.GroupVarintProjection
import ChatResponseReferenceWork.StreamingV1.OpaqueScope
import ChatResponseReferenceWork.StreamingV1.OpaqueControls
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- Exact full opaque-prefix projection at arbitrary retained group depth.
Private strict field fit derives non-closing guards, and actual skip controls
derive opaque mode at each following byte, including the final payload byte. -/
theorem group_opaque_depth_projection (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (bytes : List (BitVec 8)) (count remaining : Nat)
    (remainingBound : remaining ≤ 4096) (payloadEnough : bytes.length ≤ count) (strictFit : count < remaining)
    (modes : state.modes = lane 3) (kindShape : state.kinds.length = 4)
    (inner : state.inner = 255) (skip : state.skip = BitVec.ofNat 64 count)
    (counter : state.responseRemaining = BitVec.ofNat 64 remaining) :
    feed (eraseGroupDepth state) bytes = eraseGroupDepth (feed state bytes) := by
  induction bytes generalizing state count remaining with
  | nil => rfl
  | cons byte rest ih =>
    let next := (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state
    have notLast : TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.responseRemaining 1 = 0 := by
      rw [counter,stack_index_eq remaining 1 (by omega) (by decide)]
      exact if_neg (by simp only [List.length_cons] at payloadEnough; omega)
    have stateStep := congrArg TlsChatResponse.Event.state
      (nonkey_depth_projection state byte 3 (.inr (.inr rfl)) modes kindShape notLast)
    change feed (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (eraseGroupDepth state) byte).state rest =
      eraseGroupDepth (feed next rest)
    rw [stateStep]
    cases rest with
    | nil => rfl
    | cons following tail =>
      have countBound : count < 2^64 := by omega
      have first := opaque_prefix_inside state [byte] count countBound
        (by simp only [List.length_cons,List.length_nil] at payloadEnough ⊢; omega) modes skip
      have nextCounter : next.responseRemaining = BitVec.ofNat 64 (remaining-1) := by
        rw [opaque_remaining_step state byte modes inner,counter]
        exact BitVec.ofNat_sub_ofNat_of_le remaining 1 (by decide) (by simp only [List.length_cons] at payloadEnough; omega)
      have nextInner : next.inner = 255 := by
        have result := opaque_inner_exact state byte remaining remainingBound modes inner counter
        rw [if_neg (by simp only [List.length_cons] at payloadEnough; omega : remaining ≠ 1)] at result
        exact result
      have nextStrict : count-1 < remaining-1 := by simp only [List.length_cons] at payloadEnough; omega
      exact ih next (count-1) (remaining-1) (by omega)
        (by simp only [List.length_cons] at payloadEnough ⊢; omega) nextStrict first.1
        (key_kinds_shape state byte kindShape) nextInner first.2 nextCounter

#print axioms group_opaque_depth_projection
end ChatResponseReference.StreamingUnknownV1
