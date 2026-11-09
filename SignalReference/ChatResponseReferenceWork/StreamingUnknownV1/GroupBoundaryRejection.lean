import ChatResponseReferenceWork.StreamingUnknownV1.GroupLoopReady
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
set_option maxRecDepth 100000

/-- At a real private child end, a byte leaving an active group depth
rejects immediately; no later parent/capacity bytes can recover validity. -/
theorem core_close_active_group_reject (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (inner : state.inner = 255) (counter : state.responseRemaining = BitVec.ofNat 64 1)
    (nextDepth : TlsChatResponse.weq Word64.concrete ByteAuth.concrete
      (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.depth 0 = 0) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.valid = 0 := by
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
  rw [nextDepth]
  simp only [zeroAnd,andZero]
  rw [close]
  have closed : ByteAuth.concrete.not (ByteAuth.concrete.and 255 (ByteAuth.concrete.not 0)) = 0 := rfl
  rw [closed]
  simp only [zeroAnd,andZero]

#print axioms core_close_active_group_reject
end ChatResponseReference.StreamingUnknownV1
