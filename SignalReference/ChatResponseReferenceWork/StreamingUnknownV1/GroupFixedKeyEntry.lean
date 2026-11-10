import ChatResponseReferenceWork.StreamingUnknownV1.FixedKeyControls
import ChatResponseReferenceWork.StreamingUnknownV1.GroupFixedKeyValidity
import ChatResponseReferenceWork.StreamingUnknownV1.GroupRecognition
import ChatResponseReferenceWork.StreamingUnknownV1.GroupKeyStack
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

/-- Complete numeric field-entry relation derived from actual native nested fixed-width
key success, on one exact consumed prefix and actual native suffix. -/
theorem nested_native_fixed_key_entry (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (tag : U32) (wire : LibSignalReference.Candidate.ProstSkipKey.WireType) (depthValue budget remaining : Nat)
    (budgetBound : budget ≤ 4096) (remainingBound : remaining ≤ 4096)
    (budgetEnough : before.length ≤ budget) (physical : remaining ≤ before.length)
    (childFits : before.length-remaining < after.length)
    (modes : state.modes = lane 0) (positions : state.positions = oneHot 0)
    (kindsShape : state.kinds.length = 4) (utfShape : state.utf.length = 8)
    (value : state.value = 0) (valid : state.valid = 255) (seen : state.seen = 255) (finished : state.finished = 0)
    (inner : state.inner = 255) (depth : state.depth = BitVec.ofNat 64 depthValue)
    (budgetCounter : state.budget = BitVec.ofNat 64 budget)
    (childCounter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (positiveDepth : 0 < depthValue) (depthBound : depthValue ≤ 98) (wide : Bool) (fixedWire : wire = if wide then .SixtyFourBit else .ThirtyTwoBit)
    (fixedFits : (if wide then 8 else 4) + (before.length-after.length) ≤ remaining)
    (sourceSuccess : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Ok (tag,wire),after)) :
    ∃ consumed,
      contents before = consumed ++ contents after ∧
      responseData (feed state consumed) = responseData state ∧
      (feed state consumed).valid = 255 ∧
      (feed state consumed).modes = lane (wireLane (wireNumber wire)) ∧
      (feed state consumed).positions = oneHot 0 ∧ (feed state consumed).value = 0 ∧
      (feed state consumed).tag = BitVec.ofNat 64 tag.val ∧
      (feed state consumed).scalarKnown = 0 ∧
      (feed state consumed).kinds = [0,0,0,0] ∧
      (feed state consumed).inner = 255 ∧ (feed state consumed).depth = state.depth ∧
      (feed state consumed).stack = state.stack ∧
      (feed state consumed).budget = BitVec.ofNat 64 (budget-consumed.length) ∧
      (feed state consumed).responseRemaining = BitVec.ofNat 64 (remaining-consumed.length) ∧
      (feed state consumed).seen = 255 ∧ (feed state consumed).finished = 0 ∧
      (feed state consumed).utf.length = 8 ∧
      (feed state consumed).skip = BitVec.ofNat 64 (if wide then 8 else 4) := by
  obtain ⟨native,run,accepted⟩ := native_key_success_varint before after tag wire sourceSuccess
  obtain ⟨leading,byte,tail,span,suffix,bound,continues,terminal,tenth,nativeValue⟩ := native_success_span before after native run
  have tailLength : tail.length = after.length := by
    have result := congrArg List.length suffix
    simpa only [contents,List.length_map] using result.symm
  have inputLength : before.length = leading.length+1+after.length := by
    have result := congrArg List.length span
    simpa only [contents,List.length_map,List.length_append,List.length_cons,tailLength,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result
  have childEnough : leading.length < remaining := by omega
  have prefixBudget : leading.length < budget := by omega
  have invariant := core_prefix_invariant state leading 0 0 (by decide) (by omega) modes positions continues
  have currentPositions : (feed state leading).positions = oneHot leading.length := by simpa only [Nat.zero_add] using invariant.2.1
  have context := bounded_varint_prefix_context state leading remaining remainingBound childEnough inner childCounter continues
  have currentValue : (feed state leading).value = accumulated leading 0 0 := by simpa only [value] using invariant.2.2
  have decoded : coreDecoded (feed state leading) byte = native.bv := by
    unfold coreDecoded
    rw [currentPositions,currentValue,contribution_one_hot leading.length (by omega) byte]
    exact nativeValue.symm
  let consumed := leading ++ [byte]
  let next := (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (feed state leading) byte).state
  have consumedLength : consumed.length = leading.length+1 := by simp only [consumed,List.length_append,List.length_singleton]
  have spanComplete : contents before = consumed ++ contents after := by
    calc
      contents before = leading ++ byte::contents after := by rw [span,←suffix]
      _ = consumed ++ contents after := by simp only [consumed,List.append_assoc,List.singleton_append]
  have unfoldFeed : feed state consumed = next := by simp only [consumed,next,feed,List.foldl_append,List.foldl_cons,List.foldl_nil]
  obtain ⟨validConsumed,validSpan,completeValid⟩ := nested_native_fixed_key_valid state before after tag wire depthValue budget remaining budgetBound remainingBound
    budgetEnough physical childFits modes positions value valid seen finished inner depth budgetCounter childCounter positiveDepth depthBound wide fixedWire fixedFits sourceSuccess
  have unique : validConsumed = consumed := consumed_prefix_unique _ _ _ _ validSpan spanComplete
  subst validConsumed
  have newTag : Word64.concrete.shift (coreDecoded (feed state leading) byte) 3 = BitVec.ofNat 64 tag.val := by
    rw [decoded]; exact native_key_tag native tag wire accepted
  have nativeKind : Word64.concrete.band (coreDecoded (feed state leading) byte) (Word64.concrete.const 7) = Word64.concrete.const (wireNumber wire) := by
    rw [decoded]; exact native_key_kind native tag wire accepted
  have kindFixed : Word64.concrete.band (coreDecoded (feed state leading) byte) (Word64.concrete.const 7) =
      Word64.concrete.const (if wide then 1 else 5) := by
    rw [nativeKind,fixedWire]
    cases wide <;> rfl
  have currentNotTop := nested_depth_not_top (feed state leading) depthValue positiveDepth (by omega) (context.2.2.1.trans depth)
  have nextStack : next.stack = state.stack :=
    (native_nonstart_stack (feed state leading) byte native tag wire
      (by rw [fixedWire]; cases wide <;> intro equal <;> cases equal) decoded accepted).trans (continuing_prefix_stack state leading continues)
  have nextRemaining : next.responseRemaining = BitVec.ofNat 64 (remaining-consumed.length) := by
    rw [key_remaining_step _ byte invariant.1 context.2.2.2.1,context.2.2.2.2]
    change BitVec.ofNat 64 (remaining-leading.length) - BitVec.ofNat 64 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le (remaining-leading.length) 1 (by decide) (by omega)]
    congr 1 <;> omega
  have nextInner : next.inner = 255 := by
    have result := key_inner_exact _ byte (remaining-leading.length) (by omega) invariant.1 context.2.2.2.1 context.2.2.2.2
    rw [if_neg (by omega : remaining-leading.length ≠ 1)] at result
    exact result
  refine ⟨consumed,spanComplete,?_,completeValid,?_,?_,?_,?_,?_,?_,?_,?_,?_,feed_budget state consumed budget (by omega) budgetCounter,?_,
    (feed_seen state consumed).trans seen,(feed_finished state consumed).trans finished,feed_utf_shape state consumed utfShape,?_⟩
  · rw [unfoldFeed]
    exact (inner_key_response_data _ byte invariant.1 context.2.2.2.1).trans (nonterminal_prefix_data state leading continues)
  · rw [unfoldFeed]; exact native_key_modes _ byte native tag wire invariant.1 terminal decoded.symm accepted
  · rw [unfoldFeed]; exact terminal_position_reset _ byte 0 leading.length (by decide) invariant.1 currentPositions terminal
  · rw [unfoldFeed]; exact terminal_value_reset _ byte 0 (by decide) invariant.1 terminal
  · rw [unfoldFeed]; exact native_tag_transition _ byte native tag wire invariant.1 terminal decoded.symm accepted
  · rw [unfoldFeed]; exact nested_key_scalar_off _ byte invariant.1 currentNotTop terminal
  · rw [unfoldFeed]; exact nested_key_kinds_off _ byte invariant.1 (feed_kinds_shape state leading kindsShape) currentNotTop terminal
  · rw [unfoldFeed]; exact nextInner
  · rw [unfoldFeed]; exact (fixed_key_depth_step _ byte wide kindFixed).trans context.2.2.1
  · rw [unfoldFeed]; exact nextStack
  · rw [unfoldFeed]; exact nextRemaining
  · rw [unfoldFeed]; exact fixed_key_skip_step _ byte wide invariant.1 terminal kindFixed

#print axioms nested_native_fixed_key_entry
end ChatResponseReference.StreamingUnknownV1
