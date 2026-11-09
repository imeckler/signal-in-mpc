import ChatResponseReferenceWork.StreamingUnknownV1.StartKeyValidity
import ChatResponseReferenceWork.StreamingUnknownV1.GroupDepthStep
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

/-- Complete numeric field-entry relation derived from actual native unknown start-group
key success, on one exact consumed prefix and actual native suffix. -/
theorem unknown_native_start_key_entry (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (tag : U32) (wire : LibSignalReference.Candidate.ProstSkipKey.WireType) (budget remaining : Nat)
    (budgetBound : budget ≤ 4096) (remainingBound : remaining ≤ 4096)
    (budgetEnough : before.length ≤ budget) (physical : remaining ≤ before.length)
    (childFits : before.length-remaining < after.length)
    (modes : state.modes = lane 0) (positions : state.positions = oneHot 0)
    (kindsShape : state.kinds.length = 4) (utfShape : state.utf.length = 8)
    (value : state.value = 0) (valid : state.valid = 255) (seen : state.seen = 255) (finished : state.finished = 0)
    (inner : state.inner = 255) (depth : state.depth = 0)
    (budgetCounter : state.budget = BitVec.ofNat 64 budget)
    (childCounter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (unknownTag : 5 < tag.val) (startWire : wire = .StartGroup)
    (sourceSuccess : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Ok (tag,wire),after)) :
    ∃ consumed,
      contents before = consumed ++ contents after ∧
      responseData (feed state consumed) = responseData state ∧
      (feed state consumed).valid = 255 ∧
      (feed state consumed).modes = lane (wireLane (wireNumber wire)) ∧
      (feed state consumed).positions = oneHot 0 ∧ (feed state consumed).value = 0 ∧
      (feed state consumed).tag = BitVec.ofNat 64 tag.val ∧
      (feed state consumed).scalarKnown = (if tag.val = 1 ∨ tag.val = 2 then 255 else 0) ∧
      (feed state consumed).kinds = [0,if tag.val = 4 then 255 else 0,if tag.val = 3 then 255 else 0,if tag.val = 5 then 255 else 0] ∧
      (feed state consumed).inner = 255 ∧
      (feed state consumed).depth = Word64.concrete.add state.depth 1 ∧
      (feed state consumed).stack = TlsChatResponse.writeStack Word64.concrete ByteAuth.concrete 255 state.depth (BitVec.ofNat 64 tag.val) state.stack ∧
      (feed state consumed).budget = BitVec.ofNat 64 (budget-consumed.length) ∧
      (feed state consumed).responseRemaining = BitVec.ofNat 64 (remaining-consumed.length) ∧
      (feed state consumed).seen = 255 ∧ (feed state consumed).finished = 0 ∧
      (feed state consumed).utf.length = 8 := by
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
  obtain ⟨validConsumed,validSpan,completeValid⟩ := unknown_native_start_key_valid state before after tag wire budget remaining budgetBound remainingBound
    budgetEnough physical childFits modes positions value valid seen finished inner depth budgetCounter childCounter unknownTag startWire sourceSuccess
  have unique : validConsumed = consumed := consumed_prefix_unique _ _ _ _ validSpan spanComplete
  subst validConsumed
  have newTag : Word64.concrete.shift (coreDecoded (feed state leading) byte) 3 = BitVec.ofNat 64 tag.val := by
    rw [decoded]; exact native_key_tag native tag wire accepted
  have nativeKind : Word64.concrete.band (coreDecoded (feed state leading) byte) (Word64.concrete.const 7) = Word64.concrete.const (wireNumber wire) := by
    rw [decoded]; exact native_key_kind native tag wire accepted
  have nextDepth : next.depth = Word64.concrete.add state.depth 1 := by
    subst wire
    have result := native_key_depth_transition (feed state leading) byte native tag .StartGroup invariant.1 terminal decoded accepted
    simpa only [wireNumber,if_true,context.2.2.1] using result
  have nextStack : next.stack = TlsChatResponse.writeStack Word64.concrete ByteAuth.concrete 255 state.depth (BitVec.ofNat 64 tag.val) state.stack := by
    subst wire
    have result := native_group_push_stack (feed state leading) byte native tag invariant.1 terminal decoded accepted
    simpa only [context.2.2.1,continuing_prefix_stack state leading continues] using result
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
    (feed_seen state consumed).trans seen,(feed_finished state consumed).trans finished,feed_utf_shape state consumed utfShape⟩
  · rw [unfoldFeed]
    exact (inner_key_response_data _ byte invariant.1 context.2.2.2.1).trans (nonterminal_prefix_data state leading continues)
  · rw [unfoldFeed]; exact native_key_modes _ byte native tag wire invariant.1 terminal decoded.symm accepted
  · rw [unfoldFeed]; exact terminal_position_reset _ byte 0 leading.length (by decide) invariant.1 currentPositions terminal
  · rw [unfoldFeed]; exact terminal_value_reset _ byte 0 (by decide) invariant.1 terminal
  · rw [unfoldFeed]; exact native_tag_transition _ byte native tag wire invariant.1 terminal decoded.symm accepted
  · rw [unfoldFeed]; exact key_scalar_recognition _ byte tag true invariant.1 (context.2.2.1.trans depth) context.2.2.2.1 terminal newTag
  · rw [unfoldFeed]; exact key_field_recognition _ byte tag true invariant.1 (context.2.2.1.trans depth) context.2.2.2.1 (feed_kinds_shape state leading kindsShape) terminal newTag
  · rw [unfoldFeed]; exact nextInner
  · rw [unfoldFeed]; exact nextDepth
  · rw [unfoldFeed]; exact nextStack
  · rw [unfoldFeed]; exact nextRemaining

#print axioms unknown_native_start_key_entry
end ChatResponseReference.StreamingUnknownV1
