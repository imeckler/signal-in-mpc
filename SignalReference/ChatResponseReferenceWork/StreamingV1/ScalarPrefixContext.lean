import ChatResponseReferenceWork.StreamingV1.ScalarContext
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey

/-- Explicit bounded remaining-input invariant: no prefix byte closes the inner
response early, and the exact native tag/scalar-recognition context is retained. -/
theorem scalar_prefix_context (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (leading : List (BitVec 8)) (remaining : Nat) (capacity : remaining ≤ 4096)
    (inside : leading.length < remaining) (modes : state.modes = lane 1)
    (inner : state.inner = 255) (counter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (continues : ∀ byte ∈ leading, VarintDecode.Spqr.terminates byte = false) :
    (feed state leading).tag = state.tag ∧ (feed state leading).scalarKnown = state.scalarKnown ∧
    (feed state leading).inner = 255 ∧
    (feed state leading).responseRemaining = BitVec.ofNat 64 (remaining-leading.length) := by
  induction leading generalizing state remaining with
  | nil =>
    change state.tag = state.tag ∧ state.scalarKnown = state.scalarKnown ∧ state.inner = 255 ∧
      state.responseRemaining = BitVec.ofNat 64 (remaining-0)
    exact ⟨rfl,rfl,inner,counter⟩
  | cons byte rest ih =>
    let next := (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state
    have nonterminal := continues byte (by simp)
    have nextModes : next.modes = lane 1 := core_modes_continue state 1 (by decide) byte modes nonterminal
    have notLast : TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.responseRemaining 1 = 0 := by
      rw [counter]
      unfold TlsChatResponse.weq
      rw [word_eq_value]
      apply if_neg
      intro equal
      have numeric := congrArg BitVec.toNat equal
      have small : remaining < 2^64 := by omega
      simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] at numeric
      change remaining = 1 at numeric
      simp only [List.length_cons] at inside
      omega
    have nextInner : next.inner = 255 := scalar_continue_inner state byte modes inner notLast
    have nextCounter : next.responseRemaining = BitVec.ofNat 64 (remaining-1) := by
      rw [scalar_continue_remaining state byte modes inner,counter]
      exact BitVec.ofNat_sub_ofNat_of_le remaining 1 (by decide) (by simp only [List.length_cons] at inside; omega)
    have result := ih next (remaining-1) (by omega) (by simp only [List.length_cons] at inside; omega)
      nextModes nextInner nextCounter (by intro x member; exact continues x (by simp [member]))
    change (feed next rest).tag = state.tag ∧ (feed next rest).scalarKnown = state.scalarKnown ∧
      (feed next rest).inner = 255 ∧
      (feed next rest).responseRemaining = BitVec.ofNat 64 (remaining-(byte::rest).length)
    refine ⟨result.1.trans (scalar_continue_tag state byte modes),
      result.2.1.trans (scalar_continue_known state byte modes),result.2.2.1,?_⟩
    rw [result.2.2.2]
    congr 1
    simp only [List.length_cons]
    omega

#print axioms scalar_prefix_context
end ChatResponseReference.StreamingV1
