import ChatResponseReferenceWork.StreamingV1.ScalarPrefixValidity
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

/-- Actual native successful scalar within the declared child and public byte
budget preserves Core validity through the entire consumed field, not just its
value. All terminal/count/strict-tenth facts are derived from source execution. -/
theorem native_scalar_success_valid (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (native : U64) (budget remaining : Nat)
    (budgetBound : budget ≤ 4096) (remainingBound : remaining ≤ 4096)
    (budgetEnough : before.length ≤ budget) (physical : remaining ≤ before.length)
    (childFits : before.length-remaining ≤ after.length)
    (modes : state.modes = lane 1) (positions : state.positions = oneHot 0)
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
  have prefixValid := scalar_prefix_valid state leading 0 budget remaining (by omega) budgetBound remainingBound
    prefixBudget childEnough modes positions valid seen finished inner budgetCounter childCounter continues
  have invariant := core_prefix_invariant state leading 1 0 (by decide) (by omega) modes positions continues
  have currentPositions : (feed state leading).positions = oneHot leading.length := by simpa only [Nat.zero_add] using invariant.2.1
  have context := bounded_varint_prefix_context state leading remaining remainingBound childEnough inner childCounter continues
  have currentBudget := feed_budget state leading budget (by omega) budgetCounter
  have budgetLive := positive_budget (feed state leading) (budget-leading.length) (by omega) (by omega) currentBudget
  have result := scalar_terminal_valid (feed state leading) byte leading.length (by omega) invariant.1 currentPositions
    prefixValid ((feed_seen state leading).trans seen) ((feed_finished state leading).trans finished)
    budgetLive (context.2.2.1.trans depth) terminal tenth
  let consumed := leading ++ [byte]
  refine ⟨consumed,?_,?_⟩
  · calc
      contents before = leading ++ byte::contents after := by rw [span,←suffix]
      _ = consumed ++ contents after := by simp only [consumed,List.append_assoc,List.singleton_append]
  · simpa only [consumed,feed,List.foldl_append,List.foldl_cons,List.foldl_nil] using result

#print axioms native_scalar_success_valid
end ChatResponseReference.StreamingV1
