import ChatResponseReferenceWork.StreamingUnknownV1.OpaqueValidity
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey

private theorem remaining_not_one (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (remaining : Nat) (bounded : remaining ≤ 4096) (positive : 1 < remaining)
    (counter : state.responseRemaining = BitVec.ofNat 64 remaining) :
    TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.responseRemaining 1 = 0 := by
  rw [counter]
  unfold TlsChatResponse.weq
  rw [word_eq_value]
  apply if_neg
  intro equal
  have numeric := congrArg BitVec.toNat equal
  have small : remaining < 2^64 := by omega
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] at numeric
  change remaining = 1 at numeric
  omega

theorem unknown_opaque_payload_step_valid (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (byte : BitVec 8) (count budget remaining : Nat)
    (budgetBound : budget ≤ 4096) (remainingBound : remaining ≤ 4096)
    (budgetPositive : 0 < budget) (countPositive : 0 < count) (childEnough : count ≤ remaining)
    (modes : state.modes = lane 3) (kinds : state.kinds = [0,0,0,0])
    (valid : state.valid = 255) (seen : state.seen = 255) (finished : state.finished = 0)
    (depth : state.depth = 0) (skip : state.skip = BitVec.ofNat 64 count)
    (budgetCounter : state.budget = BitVec.ofNat 64 budget) (childCounter : state.responseRemaining = BitVec.ofNat 64 remaining) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.valid = 255 := by
  have budgetLive := positive_budget state budget budgetBound budgetPositive budgetCounter
  apply unknown_opaque_byte_valid state byte modes kinds valid seen finished budgetLive depth
  by_cases last : count = 1
  · exact .inr (by rw [skip,last])
  · exact .inl (remaining_not_one state remaining remainingBound (by omega) childCounter)

/-- Every proper/exact prefix of a physically supplied bounded unknown-field payload
preserves actual Core validity, for arbitrary body bytes. -/
theorem unknown_opaque_payload_prefix_valid (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (bytes : List (BitVec 8)) (count budget remaining : Nat)
    (budgetBound : budget ≤ 4096) (remainingBound : remaining ≤ 4096)
    (budgetEnough : bytes.length ≤ budget) (payloadEnough : bytes.length ≤ count) (childEnough : count ≤ remaining)
    (modes : state.modes = lane 3) (kinds : state.kinds = [0,0,0,0])
    (valid : state.valid = 255) (seen : state.seen = 255) (finished : state.finished = 0)
    (inner : state.inner = 255) (depth : state.depth = 0) (skip : state.skip = BitVec.ofNat 64 count)
    (budgetCounter : state.budget = BitVec.ofNat 64 budget) (childCounter : state.responseRemaining = BitVec.ofNat 64 remaining) :
    (feed state bytes).valid = 255 := by
  induction bytes generalizing state count budget remaining with
  | nil => exact valid
  | cons byte rest ih =>
    let next := (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state
    have nextValid : next.valid = 255 := unknown_opaque_payload_step_valid state byte count budget remaining budgetBound remainingBound
      (by simp only [List.length_cons] at budgetEnough; omega) (by simp only [List.length_cons] at payloadEnough; omega)
      childEnough modes kinds valid seen finished depth skip budgetCounter childCounter
    cases rest with
    | nil => exact nextValid
    | cons following tail =>
      have notLast := remaining_not_one state remaining remainingBound (by simp only [List.length_cons] at payloadEnough; omega) childCounter
      have countBound : count < 2^64 := by omega
      have first := opaque_prefix_inside state [byte] count countBound (by simp only [List.length_cons,List.length_nil] at *; omega) modes skip
      have nextModes : next.modes = lane 3 := first.1
      have nextSkip : next.skip = BitVec.ofNat 64 (count-1) := first.2
      have nextKinds : next.kinds = [0,0,0,0] := (opaque_kinds_step state byte modes (by rw [kinds]; rfl)).trans kinds
      have nextInner : next.inner = 255 := opaque_inner_step state byte modes inner notLast
      have nextDepth : next.depth = 0 := (opaque_depth_step state byte modes).trans depth
      have nextBudget : next.budget = BitVec.ofNat 64 (budget-1) := by
        rw [step_budget state byte,budgetCounter]
        exact BitVec.ofNat_sub_ofNat_of_le budget 1 (by decide) (by simp only [List.length_cons] at budgetEnough; omega)
      have nextRemaining : next.responseRemaining = BitVec.ofNat 64 (remaining-1) := by
        rw [opaque_remaining_step state byte modes inner,childCounter]
        exact BitVec.ofNat_sub_ofNat_of_le remaining 1 (by decide) (by simp only [List.length_cons] at payloadEnough; omega)
      exact ih next (count-1) (budget-1) (remaining-1) (by omega) (by omega)
        (by simp only [List.length_cons] at budgetEnough ⊢; omega) (by simp only [List.length_cons] at payloadEnough ⊢; omega) (by omega)
        nextModes nextKinds nextValid seen finished nextInner nextDepth nextSkip nextBudget nextRemaining

#print axioms unknown_opaque_payload_step_valid
#print axioms unknown_opaque_payload_prefix_valid
end ChatResponseReference.StreamingUnknownV1
