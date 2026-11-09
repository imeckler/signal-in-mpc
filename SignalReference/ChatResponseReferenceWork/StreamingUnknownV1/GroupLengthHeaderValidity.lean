import ChatResponseReferenceWork.StreamingUnknownV1.GroupVarintProjection
import ChatResponseReferenceWork.StreamingUnknownV1.LengthHeaderValidity
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- Actual native length header inside any active group preserves validity when
its complete field remains strictly inside the private child. Group depth is
retained in the real state; the proved projection reuses the checked length-header
terminal proof without presuming group parsing or primitive correctness. -/
theorem group_native_length_header_valid (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (native : U64) (budget remaining : Nat)
    (budgetBound : budget ≤ 4096) (remainingBound : remaining ≤ 4096)
    (budgetEnough : before.length ≤ budget) (physical : remaining ≤ before.length)
    (strictFit : native.val + (before.length-after.length) < remaining)
    (modes : state.modes = lane 2) (positions : state.positions = oneHot 0)
    (kindShape : state.kinds.length = 4) (kinds : state.kinds = [0,0,0,0]) (value : state.value = 0)
    (valid : state.valid = 255) (seen : state.seen = 255) (finished : state.finished = 0)
    (inner : state.inner = 255)
    (budgetCounter : state.budget = BitVec.ofNat 64 budget)
    (childCounter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (actual : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    ∃ consumed,
      contents before = consumed ++ contents after ∧ (feed state consumed).valid = 255 := by
  obtain ⟨leading,byte,tail,span,suffix,bound,continues,terminal,tenth,nativeValue⟩ := native_success_span before after native actual
  have tailLength : tail.length = after.length := by
    have result := congrArg List.length suffix
    simpa only [contents,List.length_map] using result.symm
  have inputLength : before.length = leading.length+1+after.length := by
    have result := congrArg List.length span
    simpa only [contents,List.length_map,List.length_append,List.length_cons,tailLength,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result
  let consumed := leading ++ [byte]
  have consumedSpan : contents before = consumed ++ contents after := by
    calc
      contents before = leading ++ byte::contents after := by rw [span,←suffix]
      _ = consumed ++ contents after := by simp only [consumed,List.append_assoc,List.singleton_append]
  obtain ⟨flatConsumed,flatSpan,flatValid⟩ := native_unknown_length_header_valid (eraseGroupDepth state) before after native budget remaining budgetBound remainingBound
    budgetEnough physical (by omega) modes positions value kinds valid seen finished inner rfl budgetCounter childCounter actual
  have same : flatConsumed = consumed := consumed_prefix_unique _ _ _ _ flatSpan consumedSpan
  subst flatConsumed
  have projection := group_varint_depth_projection state leading byte 2 remaining (.inr rfl) modes kindShape inner remainingBound
    (by omega) childCounter continues
  change (feed (eraseGroupDepth state) consumed).valid = 255 at flatValid
  rw [projection] at flatValid
  exact ⟨consumed,consumedSpan,flatValid⟩

#print axioms group_native_length_header_valid
end ChatResponseReference.StreamingUnknownV1
