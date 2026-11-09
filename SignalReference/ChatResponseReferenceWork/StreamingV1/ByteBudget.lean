import ChatResponseReferenceWork.StreamingV1.ScalarValidity
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey

theorem step_budget (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.budget =
      Word64.concrete.sub state.budget 1 := rfl

theorem feed_budget (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (bytes : List (BitVec 8))
    (budget : Nat) (inside : bytes.length ≤ budget) (counter : state.budget = BitVec.ofNat 64 budget) :
    (feed state bytes).budget = BitVec.ofNat 64 (budget-bytes.length) := by
  induction bytes generalizing state budget with
  | nil => exact counter
  | cons byte rest ih =>
    let next := (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state
    have nextCounter : next.budget = BitVec.ofNat 64 (budget-1) := by
      rw [step_budget state byte,counter]
      exact BitVec.ofNat_sub_ofNat_of_le budget 1 (by decide) (by simp only [List.length_cons] at inside; omega)
    have result := ih next (budget-1) (by simp only [List.length_cons] at inside; omega) nextCounter
    change (feed next rest).budget = _
    rw [result]
    congr 1 <;> (simp only [List.length_cons]; omega)

theorem feed_seen (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (bytes : List (BitVec 8)) :
    (feed state bytes).seen = state.seen := by
  induction bytes generalizing state with
  | nil => rfl
  | cons byte rest ih => exact ih _

theorem feed_finished (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (bytes : List (BitVec 8)) :
    (feed state bytes).finished = state.finished := by
  induction bytes generalizing state with
  | nil => rfl
  | cons byte rest ih => exact ih _

theorem positive_budget (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (budget : Nat)
    (bounded : budget ≤ 4096) (positive : 0 < budget) (counter : state.budget = BitVec.ofNat 64 budget) :
    TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.budget 0 = 0 := by
  rw [counter]
  unfold TlsChatResponse.weq
  rw [word_eq_value]
  apply if_neg
  intro equal
  have numeric := congrArg BitVec.toNat equal
  have small : budget < 2^64 := by omega
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] at numeric
  change budget = 0 at numeric
  omega

#print axioms step_budget
#print axioms feed_budget
#print axioms feed_seen
#print axioms feed_finished
#print axioms positive_budget
end ChatResponseReference.StreamingV1
