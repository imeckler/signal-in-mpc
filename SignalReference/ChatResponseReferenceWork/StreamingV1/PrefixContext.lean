import ChatResponseReferenceWork.StreamingV1.VarintContext
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey

/-- Explicit bounded remaining-input invariant: no prefix byte closes the inner
response early, and the exact native tag/scalar-recognition context is retained. -/
theorem bounded_varint_prefix_context (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (leading : List (BitVec 8)) (remaining : Nat) (capacity : remaining ≤ 4096)
    (inside : leading.length < remaining)
    (inner : state.inner = 255) (counter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (continues : ∀ byte ∈ leading, VarintDecode.Spqr.terminates byte = false) :
    (feed state leading).tag = state.tag ∧ (feed state leading).scalarKnown = state.scalarKnown ∧
    (feed state leading).depth = state.depth ∧ (feed state leading).inner = 255 ∧
    (feed state leading).responseRemaining = BitVec.ofNat 64 (remaining-leading.length) := by
  induction leading generalizing state remaining with
  | nil =>
    change state.tag = state.tag ∧ state.scalarKnown = state.scalarKnown ∧ state.depth = state.depth ∧ state.inner = 255 ∧
      state.responseRemaining = BitVec.ofNat 64 (remaining-0)
    exact ⟨rfl,rfl,rfl,inner,counter⟩
  | cons byte rest ih =>
    let next := (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state
    have nonterminal := continues byte (by simp)
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
    have notClosing : ByteAuth.concrete.and state.inner
        (TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.responseRemaining 1) = 0 := by rw [inner,notLast]; rfl
    have nextInner : next.inner = 255 := (nonterminal_inner state byte nonterminal notClosing).trans inner
    have nextCounter : next.responseRemaining = BitVec.ofNat 64 (remaining-1) := by
      rw [nonterminal_remaining state byte nonterminal inner,counter]
      exact BitVec.ofNat_sub_ofNat_of_le remaining 1 (by decide) (by simp only [List.length_cons] at inside; omega)
    have result := ih next (remaining-1) (by omega) (by simp only [List.length_cons] at inside; omega)
      nextInner nextCounter (by intro x member; exact continues x (by simp [member]))
    change (feed next rest).tag = state.tag ∧ (feed next rest).scalarKnown = state.scalarKnown ∧
      (feed next rest).depth = state.depth ∧ (feed next rest).inner = 255 ∧
      (feed next rest).responseRemaining = BitVec.ofNat 64 (remaining-(byte::rest).length)
    refine ⟨result.1.trans (nonterminal_tag state byte nonterminal),
      result.2.1.trans (nonterminal_known state byte nonterminal),
      result.2.2.1.trans (nonterminal_depth state byte nonterminal),result.2.2.2.1,?_⟩
    rw [result.2.2.2.2]
    congr 1
    simp only [List.length_cons]
    omega

/-- At the outer envelope no response counter can close a continuing prefix. -/
theorem outer_varint_prefix_context (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (leading : List (BitVec 8)) (inner : state.inner = 0)
    (continues : ∀ byte ∈ leading, VarintDecode.Spqr.terminates byte = false) :
    (feed state leading).tag = state.tag ∧ (feed state leading).scalarKnown = state.scalarKnown ∧
    (feed state leading).depth = state.depth ∧ (feed state leading).inner = 0 := by
  induction leading generalizing state with
  | nil => exact ⟨rfl,rfl,rfl,inner⟩
  | cons byte rest ih =>
    let next := (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state
    have nonterminal := continues byte (by simp)
    have notClosing : ByteAuth.concrete.and state.inner
        (TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.responseRemaining 1) = 0 := by
      rw [inner]; exact BitVec.zero_and
    have nextInner : next.inner = 0 := (nonterminal_inner state byte nonterminal notClosing).trans inner
    have result := ih next nextInner (by intro x member; exact continues x (by simp [member]))
    exact ⟨result.1.trans (nonterminal_tag state byte nonterminal),
      result.2.1.trans (nonterminal_known state byte nonterminal),
      result.2.2.1.trans (nonterminal_depth state byte nonterminal),result.2.2.2⟩

#print axioms bounded_varint_prefix_context
#print axioms outer_varint_prefix_context
end ChatResponseReference.StreamingV1
