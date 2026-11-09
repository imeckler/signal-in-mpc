import ChatResponseReferenceWork.StreamingV1.NativeBodyData
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

def availableLength (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) : BitVec 64 :=
  Word64.concrete.select state.inner (Word64.concrete.sub state.responseRemaining 1)
    (Word64.concrete.sub state.budget 1)

/-- Failed actual remaining-input guard rejects every length-delimited field. -/
theorem core_length_reject (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 2) (terminal : VarintDecode.Spqr.terminates byte = true)
    (tooLong : Word64.concrete.ule (coreDecoded state byte) (availableLength state) = 0) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.valid = 0 := by
  have ended : ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) = 255 := by rw [terminal_exact byte,terminal]; rfl
  change ByteAuth.concrete.and state.valid
    (ByteAuth.concrete.and state.seen (ByteAuth.concrete.and (ByteAuth.concrete.not state.finished)
      (ByteAuth.concrete.and _ (ByteAuth.concrete.and _ (ByteAuth.concrete.and _ (ByteAuth.concrete.and _
        (ByteAuth.concrete.and
          (ByteAuth.concrete.not (ByteAuth.concrete.and
            (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 2)
              (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7)))
            (ByteAuth.concrete.not (Word64.concrete.ule (coreDecoded state byte) (availableLength state))))) _))))))) = 0
  rw [tooLong,modes,ended]
  have done : ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete (lane 2) 2) 255 = 255 := rfl
  have notZero : ByteAuth.concrete.not 0 = 255 := rfl
  have hot : ByteAuth.concrete.and 255 255 = 255 := rfl
  have notHot : ByteAuth.concrete.not 255 = 0 := rfl
  have zeroAnd (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  have andZero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  rw [done,notZero,hot,notHot]
  simp only [zeroAnd,andZero]

/-- A declared child boundary inside a continuing varint is rejected at that
boundary, even if the native parent buffer physically contains later bytes. -/
theorem core_close_nonterminal_reject (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (byte : BitVec 8) (role : Nat) (roleBound : role < 3) (modes : state.modes = lane role)
    (inner : state.inner = 255) (counter : state.responseRemaining = BitVec.ofNat 64 1)
    (continues : VarintDecode.Spqr.terminates byte = false) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.valid = 0 := by
  have ended : ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) = 0 := by rw [terminal_exact byte,continues]; rfl
  have p3 : TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 3 = 0 := by
    rw [modes]
    have cases : role = 0 ∨ role = 1 ∨ role = 2 := by omega
    rcases cases with h|h|h <;> subst role <;> rfl
  change ByteAuth.concrete.and state.valid
    (ByteAuth.concrete.and state.seen (ByteAuth.concrete.and (ByteAuth.concrete.not state.finished)
      (ByteAuth.concrete.and _ (ByteAuth.concrete.and _ (ByteAuth.concrete.and _ (ByteAuth.concrete.and _
        (ByteAuth.concrete.and _ (ByteAuth.concrete.and
          (ByteAuth.concrete.not (ByteAuth.concrete.and
            (ByteAuth.concrete.and state.inner (TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.responseRemaining 1))
            (ByteAuth.concrete.not (ByteAuth.concrete.and
              (TlsWebSocketUpgrade.get ByteAuth.concrete
                (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.modes 0)
              (ByteAuth.concrete.and
                (TlsChatResponse.weq Word64.concrete ByteAuth.concrete
                  (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.depth 0)
                (TlsWebSocketUpgrade.either ByteAuth.concrete
                  (ByteAuth.concrete.and (TlsWebSocketUpgrade.any ByteAuth.concrete (state.modes.take 3))
                    (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7)))
                  (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 3))))))) _)))))))) = 0
  have andZero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  have zeroAnd (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  have orZero : TlsWebSocketUpgrade.either ByteAuth.concrete 0 0 = 0 := rfl
  have close : ByteAuth.concrete.and state.inner
      (TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.responseRemaining 1) = 255 := by rw [inner,counter]; rfl
  rw [ended,p3]
  simp only [andZero,orZero]
  rw [close]
  have closed : ByteAuth.concrete.not (ByteAuth.concrete.and 255 (ByteAuth.concrete.not 0)) = 0 := rfl
  rw [closed]
  simp only [zeroAnd,andZero]

#print axioms core_length_reject
#print axioms core_close_nonterminal_reject
end ChatResponseReference.StreamingV1
