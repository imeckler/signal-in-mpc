import ChatResponseReferenceWork.StreamingUnknownV1.GroupKeyGuard
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

/-- Actual nested native non-fixed key acceptance and actual common guards preserve
Core validity through the exact consumed key; the child must still contain value bytes. -/
theorem nested_native_nonfixed_key_valid (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (tag : U32) (wire : LibSignalReference.Candidate.ProstSkipKey.WireType) (depthValue budget remaining : Nat)
    (budgetBound : budget ≤ 4096) (remainingBound : remaining ≤ 4096)
    (budgetEnough : before.length ≤ budget) (physical : remaining ≤ before.length)
    (childFits : before.length-remaining < after.length)
    (modes : state.modes = lane 0) (positions : state.positions = oneHot 0)
    (value : state.value = 0) (valid : state.valid = 255) (seen : state.seen = 255) (finished : state.finished = 0)
    (inner : state.inner = 255) (depth : state.depth = BitVec.ofNat 64 depthValue)
    (budgetCounter : state.budget = BitVec.ofNat 64 budget)
    (childCounter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (positiveDepth : 0 < depthValue) (depthBound : depthValue ≤ 98)
    (wireClass : wire = .Varint ∨ wire = .LengthDelimited ∨ wire = .StartGroup)
    (sourceSuccess : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Ok (tag,wire),after)) :
    ∃ consumed,
      contents before = consumed ++ contents after ∧ (feed state consumed).valid = 255 := by
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
  have prefixValid := varint_prefix_valid state leading 0 budget remaining 0 (by decide) (by omega) budgetBound remainingBound
    prefixBudget childEnough modes positions valid seen finished inner budgetCounter childCounter continues
  have invariant := core_prefix_invariant state leading 0 0 (by decide) (by omega) modes positions continues
  have currentPositions : (feed state leading).positions = oneHot leading.length := by simpa only [Nat.zero_add] using invariant.2.1
  have context := bounded_varint_prefix_context state leading remaining remainingBound childEnough inner childCounter continues
  have currentBudget := feed_budget state leading budget (by omega) budgetCounter
  have budgetLive := positive_budget (feed state leading) (budget-leading.length) (by omega) (by omega) currentBudget
  have currentValue : (feed state leading).value = accumulated leading 0 0 := by simpa only [value] using invariant.2.2
  have decoded : coreDecoded (feed state leading) byte = native.bv := by
    unfold coreDecoded
    rw [currentPositions,currentValue,contribution_one_hot leading.length (by omega) byte]
    exact nativeValue.symm
  have notEnd : wire ≠ .EndGroup := by
    rcases wireClass with same|same|same <;> rw [same] <;> intro equal <;> cases equal
  have keyGood := nested_inner_native_key_good (feed state leading) byte native tag wire depthValue positiveDepth depthBound
    (context.2.2.1.trans depth) notEnd context.2.2.2.1 decoded accepted
  have fixedOff : TlsWebSocketUpgrade.either ByteAuth.concrete
      (TlsChatResponse.weq Word64.concrete ByteAuth.concrete (Word64.concrete.band (coreDecoded (feed state leading) byte) (Word64.concrete.const 7)) 1)
      (TlsChatResponse.weq Word64.concrete ByteAuth.concrete (Word64.concrete.band (coreDecoded (feed state leading) byte) (Word64.concrete.const 7)) 5) = 0 := by
    have kind : Word64.concrete.band native.bv (Word64.concrete.const 7) = Word64.concrete.const (wireNumber wire) := native_key_kind native tag wire accepted
    rw [decoded,kind]
    rcases wireClass with same|same|same <;> rw [same] <;> rfl
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
  have result := key_terminal_valid (feed state leading) byte leading.length (by omega) invariant.1 currentPositions
    prefixValid ((feed_seen state leading).trans seen) ((feed_finished state leading).trans finished)
    budgetLive notClosing keyGood fixedOff terminal tenth
  let consumed := leading ++ [byte]
  refine ⟨consumed,?_,?_⟩
  · calc
      contents before = leading ++ byte::contents after := by rw [span,←suffix]
      _ = consumed ++ contents after := by simp only [consumed,List.append_assoc,List.singleton_append]
  · simpa only [consumed,feed,List.foldl_append,List.foldl_cons,List.foldl_nil] using result

#print axioms nested_native_nonfixed_key_valid
end ChatResponseReference.StreamingUnknownV1
