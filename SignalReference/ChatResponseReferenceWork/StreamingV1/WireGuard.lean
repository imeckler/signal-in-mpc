import ChatResponseReferenceWork.StreamingV1.CompiledInactive
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-- Executable projections of the actual Core key guard, not source replacements. -/
def scalarKeyMask (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8) : BitVec 8 :=
  ByteAuth.concrete.and (TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.depth 0)
    (TlsInner.select ByteAuth.concrete state.inner
      (TlsChatResponse.wmember Word64.concrete ByteAuth.concrete (Word64.concrete.shift (coreDecoded state byte) 3) [1,2])
      (TlsChatResponse.weq Word64.concrete ByteAuth.concrete (Word64.concrete.shift (coreDecoded state byte) 3) 1))
def bytesKeyMask (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8) : BitVec 8 :=
  ByteAuth.concrete.and (TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.depth 0)
    (TlsInner.select ByteAuth.concrete state.inner
      (TlsChatResponse.wmember Word64.concrete ByteAuth.concrete (Word64.concrete.shift (coreDecoded state byte) 3) [3,4,5])
      (TlsChatResponse.wmember Word64.concrete ByteAuth.concrete (Word64.concrete.shift (coreDecoded state byte) 3) [2,3]))
def schemaWireMask (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8) : BitVec 8 :=
  TlsWebSocketUpgrade.either ByteAuth.concrete
    (ByteAuth.concrete.not (TlsWebSocketUpgrade.either ByteAuth.concrete (scalarKeyMask state byte) (bytesKeyMask state byte)))
    (TlsWebSocketUpgrade.either ByteAuth.concrete
      (ByteAuth.concrete.and (scalarKeyMask state byte)
        (TlsChatResponse.weq Word64.concrete ByteAuth.concrete (Word64.concrete.band (coreDecoded state byte) 7) 0))
      (ByteAuth.concrete.and (bytesKeyMask state byte)
        (TlsChatResponse.weq Word64.concrete ByteAuth.concrete (Word64.concrete.band (coreDecoded state byte) 7) 2)))

/-- A failed schema-wire clause forces actual Core rejection; other common key,
recursion and input guards remain represented in the actual computation. -/
theorem core_schema_wire_reject (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (byte : BitVec 8) (modes : state.modes = lane 0)
    (terminal : VarintDecode.Spqr.terminates byte = true) (invalid : schemaWireMask state byte = 0) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.valid = 0 := by
  have ended : ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) = 255 := by
    rw [terminal_exact byte,terminal]; rfl
  have zeroAnd (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  have andZero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  have bad (a b c rest : BitVec 8) : ByteAuth.concrete.and a (ByteAuth.concrete.and b
      (ByteAuth.concrete.and c (ByteAuth.concrete.and (schemaWireMask state byte) rest))) = 0 := by
    rw [invalid]
    simp only [zeroAnd,andZero]
  change ByteAuth.concrete.and state.valid
    (ByteAuth.concrete.and state.seen (ByteAuth.concrete.and (ByteAuth.concrete.not state.finished)
      (ByteAuth.concrete.and _ (ByteAuth.concrete.and _
        (ByteAuth.concrete.and
          (ByteAuth.concrete.not (ByteAuth.concrete.and
            (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0)
              (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7)))
            (ByteAuth.concrete.not (ByteAuth.concrete.and _ (ByteAuth.concrete.and _
              (ByteAuth.concrete.and _ (ByteAuth.concrete.and (schemaWireMask state byte) _))))))) _))))) = 0
  rw [bad,modes,ended]
  have notZero : ByteAuth.concrete.not 0 = 255 := rfl
  have hot : ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete (lane 0) 0) 255 = 255 := rfl
  have andHot : ByteAuth.concrete.and 255 255 = 255 := rfl
  have notHot : ByteAuth.concrete.not 255 = 0 := rfl
  rw [notZero,hot,andHot,notHot]
  simp only [zeroAnd,andZero]

#print axioms core_schema_wire_reject
end ChatResponseReference.StreamingV1
