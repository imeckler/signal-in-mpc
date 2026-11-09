import ChatResponseReferenceWork.StreamingV1.BodyFieldScoped
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey
private theorem zero_and (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
theorem scalar_inner_exact (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (remaining : Nat) (bounded : remaining ≤ 4096)
    (modes : state.modes = lane 1) (inner : state.inner = 255)
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
  have off : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 1) 2 = 0 := rfl
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

theorem scalar_depth_step (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 1) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.depth = state.depth := by
  change Word64.concrete.select
    (ByteAuth.concrete.and (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0) _) _) _
    (Word64.concrete.select
      (ByteAuth.concrete.and (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0) _) _) _ state.depth) = state.depth
  rw [modes]
  have off : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 1) 0 = 0 := rfl
  simp only [off,zero_and,Word64.select_reject]

#print axioms scalar_inner_exact
#print axioms scalar_depth_step
end ChatResponseReference.StreamingV1
