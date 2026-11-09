import ChatResponseReferenceWork.StreamingV1.ByteBudget
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey

/-- Actual scalar-prefix validity from strict position/input/child bounds.
Initial validity is an induction-state condition, not assumed parser correctness. -/
theorem scalar_prefix_valid (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (leading : List (BitVec 8)) (group budget remaining : Nat)
    (positionBound : group+leading.length ≤ 9) (budgetBound : budget ≤ 4096) (remainingBound : remaining ≤ 4096)
    (budgetEnough : leading.length < budget) (childEnough : leading.length < remaining)
    (modes : state.modes = lane 1) (positions : state.positions = oneHot group)
    (valid : state.valid = 255) (seen : state.seen = 255) (finished : state.finished = 0)
    (inner : state.inner = 255) (budgetCounter : state.budget = BitVec.ofNat 64 budget)
    (childCounter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (continues : ∀ byte ∈ leading, VarintDecode.Spqr.terminates byte = false) :
    (feed state leading).valid = 255 := by
  induction leading generalizing state group budget remaining with
  | nil => exact valid
  | cons byte rest ih =>
    have nonterminal := continues byte (by simp)
    have groupSmall : group < 9 := by simp only [List.length_cons] at positionBound; omega
    have budgetLive := positive_budget state budget budgetBound (by simp only [List.length_cons] at budgetEnough; omega) budgetCounter
    have notLast : TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.responseRemaining 1 = 0 := by
      rw [childCounter]
      unfold TlsChatResponse.weq
      rw [word_eq_value]
      apply if_neg
      intro equal
      have numeric := congrArg BitVec.toNat equal
      have small : remaining < 2^64 := by omega
      simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] at numeric
      change remaining = 1 at numeric
      simp only [List.length_cons] at childEnough
      omega
    let next := (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state
    have nextValid : next.valid = 255 := scalar_nonterminal_valid state byte group groupSmall modes positions valid seen finished budgetLive notLast nonterminal
    have nextModes : next.modes = lane 1 := core_modes_continue state 1 (by decide) byte modes nonterminal
    have nextPositions : next.positions = oneHot (group+1) := core_positions_continue state 1 group (by decide) groupSmall byte modes positions nonterminal
    have nextBudget : next.budget = BitVec.ofNat 64 (budget-1) := by
      rw [step_budget state byte,budgetCounter]
      exact BitVec.ofNat_sub_ofNat_of_le budget 1 (by decide) (by simp only [List.length_cons] at budgetEnough; omega)
    have notClosing : ByteAuth.concrete.and state.inner
        (TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.responseRemaining 1) = 0 := by rw [inner,notLast]; rfl
    have nextInner : next.inner = 255 := (nonterminal_inner state byte nonterminal notClosing).trans inner
    have nextRemaining : next.responseRemaining = BitVec.ofNat 64 (remaining-1) := by
      rw [nonterminal_remaining state byte nonterminal inner,childCounter]
      exact BitVec.ofNat_sub_ofNat_of_le remaining 1 (by decide) (by simp only [List.length_cons] at childEnough; omega)
    exact ih next (group+1) (budget-1) (remaining-1)
      (by simp only [List.length_cons] at positionBound; omega) (by omega) (by omega)
      (by simp only [List.length_cons] at budgetEnough; omega) (by simp only [List.length_cons] at childEnough; omega)
      nextModes nextPositions nextValid seen finished nextInner nextBudget nextRemaining
      (by intro x member; exact continues x (by simp [member]))

#print axioms scalar_prefix_valid
end ChatResponseReference.StreamingV1
