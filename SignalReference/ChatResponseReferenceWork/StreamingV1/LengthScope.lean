import ChatResponseReferenceWork.StreamingV1.OpaqueScope
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey
theorem length_inner_exact (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (remaining : Nat) (bounded : remaining ≤ 4096)
    (kindsOff : TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 0 = 0) (inner : state.inner = 255)
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
  have andZero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  have zeroAnd (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  have hotAnd (x : BitVec 8) : ByteAuth.concrete.and 255 x = x := BitVec.allOnes_and
  change TlsInner.select ByteAuth.concrete
    (ByteAuth.concrete.and (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 2) _)
      (TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 0)) _
    (TlsInner.select ByteAuth.concrete
      (ByteAuth.concrete.and state.inner (TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.responseRemaining 1)) 0 state.inner) = _
  rw [kindsOff,andZero,TlsInner.select_reject,inner,equal,hotAnd]
  by_cases last : remaining = 1
  · simp only [if_pos last,TlsInner.select_accept]
  · simp only [if_neg last,TlsInner.select_reject]

#print axioms length_inner_exact
end ChatResponseReference.StreamingV1
