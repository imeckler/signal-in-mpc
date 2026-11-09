import ChatResponseReferenceWork.StreamingV1.BodyEvents
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 2000000

private theorem zero_and (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
private theorem and_zero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
private theorem hot_and (x : BitVec 8) : ByteAuth.concrete.and 255 x = x := BitVec.allOnes_and
private theorem not_zero : ByteAuth.concrete.not 0 = 255 := rfl
private theorem not_hot : ByteAuth.concrete.not 255 = 0 := rfl
private theorem either_zero : TlsWebSocketUpgrade.either ByteAuth.concrete 0 0 = 0 := rfl

private theorem position_live (group : Nat) (bound : group < 10) :
    TlsWebSocketUpgrade.any ByteAuth.concrete (oneHot group) = 255 := by
  have cases : group = 0 ∨ group = 1 ∨ group = 2 ∨ group = 3 ∨ group = 4 ∨ group = 5 ∨ group = 6 ∨ group = 7 ∨ group = 8 ∨ group = 9 := by omega
  rcases cases with h|h|h|h|h|h|h|h|h|h <;> subst group <;> rfl
private theorem position_not_tenth (group : Nat) (bound : group < 9) :
    TlsWebSocketUpgrade.get ByteAuth.concrete (oneHot group) 9 = 0 := by
  have cases : group = 0 ∨ group = 1 ∨ group = 2 ∨ group = 3 ∨ group = 4 ∨ group = 5 ∨ group = 6 ∨ group = 7 ∨ group = 8 := by omega
  rcases cases with h|h|h|h|h|h|h|h|h <;> subst group <;> rfl

theorem varint_nonterminal_valid (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (byte : BitVec 8) (group role : Nat) (bound : group < 9) (roleBound : role < 3)
    (modes : state.modes = lane role) (positions : state.positions = oneHot group)
    (valid : state.valid = 255) (seen : state.seen = 255) (finished : state.finished = 0)
    (budget : TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.budget 0 = 0)
    (notClosing : TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.responseRemaining 1 = 0)
    (continues : VarintDecode.Spqr.terminates byte = false) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.valid = 255 := by
  have ended : ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) = 0 := by rw [terminal_exact byte,continues]; rfl
  have p3 : TlsWebSocketUpgrade.get ByteAuth.concrete (lane role) 3 = 0 := by
    have cases : role = 0 ∨ role = 1 ∨ role = 2 := by omega
    rcases cases with h|h|h <;> subst role <;> rfl
  have live : TlsWebSocketUpgrade.any ByteAuth.concrete state.positions = 255 := by rw [positions]; exact position_live group (by omega)
  have lastOff : TlsWebSocketUpgrade.get ByteAuth.concrete state.positions 9 = 0 := by rw [positions]; exact position_not_tenth group bound
  simp only [TlsChatResponse.step]
  rw [valid,seen,finished,modes,ended,budget,notClosing,live,lastOff]
  simp only [p3,zero_and,and_zero,hot_and,not_zero,not_hot,either_zero]

/-- Actual scalar-prefix validity from strict position/input/child bounds.
Initial validity is an induction-state condition, not assumed parser correctness. -/
theorem varint_prefix_valid (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (leading : List (BitVec 8)) (group budget remaining role : Nat) (roleBound : role < 3)
    (positionBound : group+leading.length ≤ 9) (budgetBound : budget ≤ 4096) (remainingBound : remaining ≤ 4096)
    (budgetEnough : leading.length < budget) (childEnough : leading.length < remaining)
    (modes : state.modes = lane role) (positions : state.positions = oneHot group)
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
    have nextValid : next.valid = 255 := varint_nonterminal_valid state byte group role groupSmall roleBound modes positions valid seen finished budgetLive notLast nonterminal
    have nextModes : next.modes = lane role := core_modes_continue state role roleBound byte modes nonterminal
    have nextPositions : next.positions = oneHot (group+1) := core_positions_continue state role group roleBound groupSmall byte modes positions nonterminal
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

#print axioms varint_nonterminal_valid
#print axioms varint_prefix_valid
end ChatResponseReference.StreamingV1
