import ChatResponseReferenceWork.StreamingV1.StringUtfShape
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

/-- Actual native body-length success whose entire payload fits the child
preserves Core validity through the header, including empty exact-end bodies. -/
theorem native_message_header_state (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (native : U64) (budget remaining : Nat)
    (budgetBound : budget ≤ 4096) (remainingBound : remaining ≤ 4096)
    (budgetEnough : before.length ≤ budget) (physical : remaining ≤ before.length)
    (childFits : native.val + (before.length-after.length) ≤ remaining)
    (modes : state.modes = lane 2) (positions : state.positions = oneHot 0)
    (utfShape : state.utf.length = 8) (value : state.value = 0) (kinds : state.kinds = [0,0,255,0])
    (valid : state.valid = 255) (seen : state.seen = 255) (finished : state.finished = 0)
    (inner : state.inner = 255) (depth : state.depth = 0)
    (budgetCounter : state.budget = BitVec.ofNat 64 budget)
    (childCounter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (sourceSuccess : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    ∃ consumed,
      contents before = consumed ++ contents after ∧
      (feed state consumed).valid = 255 ∧ (feed state consumed).utf = Utf8.encode .ready ∧
      (feed state consumed).budget = BitVec.ofNat 64 (budget-consumed.length) ∧
      (feed state consumed).responseRemaining = BitVec.ofNat 64 (remaining-consumed.length) ∧
      (feed state consumed).kinds = [0,0,255,0] ∧ (feed state consumed).depth = 0 ∧
      (feed state consumed).skip = native.bv ∧
      (feed state consumed).modes = (if native.val = 0 then lane 0 else lane 3) ∧
      (native.val ≠ 0 → (feed state consumed).inner = 255) := by
  obtain ⟨leading,byte,tail,span,suffix,bound,continues,terminal,tenth,nativeValue⟩ := native_success_span before after native sourceSuccess
  have tailLength : tail.length = after.length := by
    have result := congrArg List.length suffix
    simpa only [contents,List.length_map] using result.symm
  have inputLength : before.length = leading.length+1+after.length := by
    have result := congrArg List.length span
    simpa only [contents,List.length_map,List.length_append,List.length_cons,tailLength,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result
  have childEnough : leading.length < remaining := by omega
  have prefixBudget : leading.length < budget := by omega
  have prefixValid := varint_prefix_valid state leading 0 budget remaining 2 (by decide) (by omega) budgetBound remainingBound
    prefixBudget childEnough modes positions valid seen finished inner budgetCounter childCounter continues
  have invariant := core_prefix_invariant state leading 2 0 (by decide) (by omega) modes positions continues
  have currentPositions : (feed state leading).positions = oneHot leading.length := by simpa only [Nat.zero_add] using invariant.2.1
  have context := bounded_varint_prefix_context state leading remaining remainingBound childEnough inner childCounter continues
  have currentBudget := feed_budget state leading budget (by omega) budgetCounter
  have budgetLive := positive_budget (feed state leading) (budget-leading.length) (by omega) (by omega) currentBudget
  have currentKinds : (feed state leading).kinds = [0,0,255,0] :=
    (prefix_kinds state leading continues (by rw [kinds]; rfl)).trans kinds
  have currentValue : (feed state leading).value = accumulated leading 0 0 := by
    simpa only [value] using invariant.2.2
  have decoded : coreDecoded (feed state leading) byte = native.bv := by
    unfold coreDecoded
    rw [currentPositions,currentValue,contribution_one_hot leading.length (by omega) byte]
    exact nativeValue.symm
  obtain ⟨checkedHeader,checkedSpan,checkedValid⟩ := native_message_header_valid state before after native budget remaining
    budgetBound remainingBound budgetEnough physical childFits modes positions value kinds valid seen finished inner depth budgetCounter childCounter sourceSuccess
  let consumed := leading ++ [byte]
  have headerSpan : contents before = consumed ++ contents after := by
    calc
      contents before = leading ++ byte::contents after := by rw [span,←suffix]
      _ = consumed ++ contents after := by simp only [consumed,List.append_assoc,List.singleton_append]
  have unique : checkedHeader = consumed := consumed_prefix_unique _ _ _ _ checkedSpan headerSpan
  subst checkedHeader
  let next := (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (feed state leading) byte).state
  have unfoldFeed : feed state consumed = next := by
    simp only [consumed,next,feed,List.foldl_append,List.foldl_cons,List.foldl_nil]
  have length : consumed.length = leading.length+1 := by simp only [consumed,List.length_append,List.length_singleton]
  have remainingNext : next.responseRemaining = BitVec.ofNat 64 (remaining-consumed.length) := by
    rw [message_length_remaining_step _ byte invariant.1 currentKinds context.2.2.2.1,context.2.2.2.2]
    change BitVec.ofNat 64 (remaining-leading.length) - BitVec.ofNat 64 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le (remaining-leading.length) 1 (by decide) (by omega)]
    congr 1 <;> omega
  have modesNext : next.modes = if native.val = 0 then lane 0 else lane 3 := by
    rw [message_mode_terminal _ byte invariant.1 currentKinds terminal,decoded]
    have zeroIff : native.bv = BitVec.ofNat 64 0 ↔ native.val = 0 := by
      constructor
      · intro equal; have numeric := congrArg BitVec.toNat equal; simpa only [UScalar.bv_toNat,BitVec.toNat_ofNat] using numeric
      · intro equal; apply BitVec.eq_of_toNat_eq; simp only [UScalar.bv_toNat,BitVec.toNat_ofNat,equal]
    simp only [zeroIff]
  refine ⟨consumed,headerSpan,checkedValid,?_,feed_budget state consumed budget (by omega) budgetCounter,?_,?_,?_,?_,?_,?_⟩
  · rw [unfoldFeed]; exact string_utf_reset _ byte invariant.1 terminal (feed_utf_shape state leading utfShape)
  · rw [unfoldFeed]; exact remainingNext
  · rw [unfoldFeed]; exact (message_length_kinds_step _ byte invariant.1 (by rw [currentKinds]; rfl)).trans currentKinds
  · rw [unfoldFeed]; exact (message_length_depth_step _ byte invariant.1).trans (context.2.2.1.trans depth)
  · rw [unfoldFeed]; exact (length_skip_terminal _ byte invariant.1 terminal).trans decoded
  · rw [unfoldFeed]; exact modesNext
  · intro nonempty
    have notClosing : TlsChatResponse.weq Word64.concrete ByteAuth.concrete (feed state leading).responseRemaining 1 = 0 := by
      rw [context.2.2.2.2]
      unfold TlsChatResponse.weq
      rw [word_eq_value]
      apply if_neg
      intro equal
      have numeric := congrArg BitVec.toNat equal
      have small : remaining-leading.length < 2^64 := by omega
      simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] at numeric
      change remaining-leading.length = 1 at numeric
      omega
    rw [unfoldFeed]
    exact message_length_inner_step _ byte invariant.1 currentKinds context.2.2.2.1 notClosing

#print axioms native_message_header_state
end ChatResponseReference.StreamingV1
