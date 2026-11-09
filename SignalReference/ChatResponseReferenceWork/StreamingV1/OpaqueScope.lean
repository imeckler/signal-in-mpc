import ChatResponseReferenceWork.StreamingV1.MessageFieldComplete
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey

theorem opaque_inner_exact (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (remaining : Nat) (bounded : remaining ≤ 4096)
    (modes : state.modes = lane 3) (inner : state.inner = 255)
    (counter : state.responseRemaining = BitVec.ofNat 64 remaining) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.inner =
      if remaining = 1 then 0 else 255 := by
  have equal : TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.responseRemaining 1 =
      if remaining = 1 then 255 else 0 := by
    rw [counter]
    unfold TlsChatResponse.weq
    rw [word_eq_value]
    have iff : BitVec.ofNat 64 remaining = Word64.concrete.const 1 ↔ remaining = 1 := by
      constructor
      · intro h
        have numeric := congrArg BitVec.toNat h
        have small : remaining < 2^64 := by omega
        simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] at numeric
        exact numeric
      · intro h; rw [h]; rfl
    simp only [iff]
  have off : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 3) 2 = 0 := rfl
  have zeroAnd (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  have hotAnd (x : BitVec 8) : ByteAuth.concrete.and 255 x = x := BitVec.allOnes_and
  change TlsInner.select ByteAuth.concrete
    (ByteAuth.concrete.and (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 2) _) _) _
    (TlsInner.select ByteAuth.concrete
      (ByteAuth.concrete.and state.inner (TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.responseRemaining 1)) 0 state.inner) = _
  rw [modes,off,zeroAnd,zeroAnd,TlsInner.select_reject,inner,equal,hotAnd]
  by_cases last : remaining = 1
  · simp only [if_pos last,TlsInner.select_accept]
  · simp only [if_neg last,TlsInner.select_reject]

/-- Exact child-scope/cursor projection through every bounded opaque prefix.
The counter closes only at the real child end, independently of validity. -/
theorem opaque_scope_prefix (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (bytes : List (BitVec 8)) (count remaining : Nat)
    (bounded : remaining ≤ 4096) (positive : 0 < remaining)
    (fits : bytes.length ≤ count) (childEnough : count ≤ remaining)
    (modes : state.modes = lane 3) (skip : state.skip = BitVec.ofNat 64 count)
    (inner : state.inner = 255) (counter : state.responseRemaining = BitVec.ofNat 64 remaining) :
    (feed state bytes).responseRemaining = BitVec.ofNat 64 (remaining-bytes.length) ∧
    (feed state bytes).inner = (if bytes.length = remaining then 0 else 255) ∧
    (feed state bytes).depth = state.depth := by
  induction bytes generalizing state count remaining with
  | nil =>
    refine ⟨counter,?_,rfl⟩
    simpa only [feed,List.foldl_nil,List.length_nil,if_neg (by omega : 0 ≠ remaining)] using inner
  | cons byte rest ih =>
    let next := (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state
    have nextRemaining : next.responseRemaining = BitVec.ofNat 64 (remaining-1) := by
      rw [opaque_remaining_step state byte modes inner,counter]
      exact BitVec.ofNat_sub_ofNat_of_le remaining 1 (by decide) (by omega)
    have nextInner := opaque_inner_exact state byte remaining bounded modes inner counter
    have nextDepth : next.depth = state.depth := opaque_depth_step state byte modes
    cases rest with
    | nil =>
      exact ⟨nextRemaining,by simpa only [next,feed,List.foldl_cons,List.foldl_nil,List.length_cons,List.length_nil,Nat.zero_add,eq_comm] using nextInner,nextDepth⟩
    | cons following tail =>
      have countBound : count < 2^64 := by omega
      have first := opaque_prefix_inside state [byte] count countBound (by simp only [List.length_cons,List.length_nil] at fits ⊢; omega) modes skip
      have currentInner : next.inner = 255 := by rw [if_neg (by simp only [List.length_cons] at fits; omega)] at nextInner; exact nextInner
      have result := ih next (count-1) (remaining-1) (by omega) (by simp only [List.length_cons] at fits; omega)
        (by simp only [List.length_cons] at fits ⊢; omega) (by omega) first.1 first.2 currentInner nextRemaining
      refine ⟨?_,?_,result.2.2.trans nextDepth⟩
      · simpa only [next,feed,List.foldl_cons,List.length_cons,Nat.sub_sub,Nat.add_comm] using result.1
      · have equal : (following::tail).length = remaining-1 ↔ (byte::following::tail).length = remaining := by simp only [List.length_cons] at *; omega
        simpa only [next,feed,List.foldl_cons,equal] using result.2.1

#print axioms opaque_inner_exact
#print axioms opaque_scope_prefix
end ChatResponseReference.StreamingV1
