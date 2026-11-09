import ChatResponseReferenceWork.StreamingV1.MessageLengthValidity
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

/-- Actual native body-length success whose entire payload fits the child
preserves Core validity through the header, including empty exact-end bodies. -/
theorem native_message_header_valid (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (native : U64) (budget remaining : Nat)
    (budgetBound : budget ≤ 4096) (remainingBound : remaining ≤ 4096)
    (budgetEnough : before.length ≤ budget) (physical : remaining ≤ before.length)
    (childFits : native.val + (before.length-after.length) ≤ remaining)
    (modes : state.modes = lane 2) (positions : state.positions = oneHot 0)
    (value : state.value = 0) (kinds : state.kinds = [0,0,255,0])
    (valid : state.valid = 255) (seen : state.seen = 255) (finished : state.finished = 0)
    (inner : state.inner = 255) (depth : state.depth = 0)
    (budgetCounter : state.budget = BitVec.ofNat 64 budget)
    (childCounter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (sourceSuccess : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    ∃ consumed,
      contents before = consumed ++ contents after ∧ (feed state consumed).valid = 255 := by
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
  have available : availableLength (feed state leading) = BitVec.ofNat 64 (remaining-(leading.length+1)) := by
    unfold availableLength
    rw [context.2.2.2.1,Word64.select_accept,context.2.2.2.2]
    change BitVec.ofNat 64 (remaining-leading.length) - BitVec.ofNat 64 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le (remaining-leading.length) 1 (by decide) (by omega)]
    congr 1 <;> omega
  have fits : Word64.concrete.ule (coreDecoded (feed state leading) byte) (availableLength (feed state leading)) = 255 := by
    rw [decoded,available,Word64.ule_value]
    have small : remaining-(leading.length+1) < 2^64 := by omega
    simp only [UScalar.bv_toNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
    exact if_pos (by omega)
  have result : (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (feed state leading) byte).state.valid = 255 := by
    by_cases empty : native.val = 0
    · have emptyBits : coreDecoded (feed state leading) byte = BitVec.ofNat 64 0 := by
        rw [decoded]
        apply BitVec.eq_of_toNat_eq
        simp only [UScalar.bv_toNat,BitVec.toNat_ofNat,empty]
      exact empty_message_length_valid _ byte leading.length (by omega) invariant.1 currentPositions
        prefixValid ((feed_seen state leading).trans seen) ((feed_finished state leading).trans finished)
        budgetLive (context.2.2.1.trans depth) currentKinds emptyBits fits terminal tenth
    · have notClosing : TlsChatResponse.weq Word64.concrete ByteAuth.concrete (feed state leading).responseRemaining 1 = 0 := by
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
      exact message_length_nonclosing_valid _ byte leading.length (by omega) invariant.1 currentPositions
        prefixValid ((feed_seen state leading).trans seen) ((feed_finished state leading).trans finished)
        budgetLive (context.2.2.1.trans depth) currentKinds notClosing fits terminal tenth
  let consumed := leading ++ [byte]
  refine ⟨consumed,?_,?_⟩
  · calc
      contents before = leading ++ byte::contents after := by rw [span,←suffix]
      _ = consumed ++ contents after := by simp only [consumed,List.append_assoc,List.singleton_append]
  · simpa only [consumed,feed,List.foldl_append,List.foldl_cons,List.foldl_nil] using result

#print axioms native_message_header_valid
end ChatResponseReference.StreamingV1
