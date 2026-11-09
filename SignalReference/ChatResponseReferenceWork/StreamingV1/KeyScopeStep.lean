import ChatResponseReferenceWork.StreamingV1.NativeKnownKeyValidity
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey
theorem key_inner_exact (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (remaining : Nat) (bounded : remaining ≤ 4096)
    (modes : state.modes = lane 0) (inner : state.inner = 255)
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
  have off : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 0) 2 = 0 := rfl
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

theorem key_remaining_step (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (byte : BitVec 8) (modes : state.modes = lane 0) (inner : state.inner = 255) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.responseRemaining =
      Word64.concrete.sub state.responseRemaining 1 := by
  change Word64.concrete.select
    (ByteAuth.concrete.and
      (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 2) _)
      (TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 0)) _
    (Word64.concrete.select state.inner (Word64.concrete.sub state.responseRemaining 1) state.responseRemaining) = _
  rw [modes,inner]
  have zero (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  have laneTwo : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 0) 2 = 0 := rfl
  rw [laneTwo,zero,zero,Word64.select_reject,Word64.select_accept]


theorem key_known_depth_step (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (number : Nat) (wire : number = 0 ∨ number = 2)
    (kind : Word64.concrete.band (coreDecoded state byte) (Word64.concrete.const 7) = Word64.concrete.const number) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.depth = state.depth := by
  change Word64.concrete.select
    (ByteAuth.concrete.and (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0)
      (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7)))
      (TlsChatResponse.weq Word64.concrete ByteAuth.concrete (Word64.concrete.band (coreDecoded state byte) (Word64.concrete.const 7)) 3)) _
    (Word64.concrete.select
      (ByteAuth.concrete.and (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0)
        (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7)))
        (TlsChatResponse.weq Word64.concrete ByteAuth.concrete (Word64.concrete.band (coreDecoded state byte) (Word64.concrete.const 7)) 4)) _ state.depth) = _
  rw [kind]
  have andZero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  rcases wire with h|h
  · subst number
    have notStart : TlsChatResponse.weq Word64.concrete ByteAuth.concrete (Word64.concrete.const 0) 3 = 0 := rfl
    have notEnd : TlsChatResponse.weq Word64.concrete ByteAuth.concrete (Word64.concrete.const 0) 4 = 0 := rfl
    rw [notStart,notEnd]
    simp only [andZero,Word64.select_reject]
  · subst number
    have notStart : TlsChatResponse.weq Word64.concrete ByteAuth.concrete (Word64.concrete.const 2) 3 = 0 := rfl
    have notEnd : TlsChatResponse.weq Word64.concrete ByteAuth.concrete (Word64.concrete.const 2) 4 = 0 := rfl
    rw [notStart,notEnd]
    simp only [andZero,Word64.select_reject]

#print axioms key_inner_exact
#print axioms key_remaining_step
#print axioms key_known_depth_step
end ChatResponseReference.StreamingV1
