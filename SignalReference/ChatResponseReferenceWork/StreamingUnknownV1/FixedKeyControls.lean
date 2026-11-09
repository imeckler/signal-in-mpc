import ChatResponseReferenceWork.StreamingUnknownV1.FixedKeyValidity
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem fixed_key_depth_step (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8) (wide : Bool)
    (kind : Word64.concrete.band (coreDecoded state byte) (Word64.concrete.const 7) = Word64.concrete.const (if wide then 1 else 5)) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.depth = state.depth := by
  have notThree : TlsChatResponse.weq Word64.concrete ByteAuth.concrete
      (Word64.concrete.band (coreDecoded state byte) (Word64.concrete.const 7)) 3 = 0 := by rw [kind]; cases wide <;> rfl
  have notFour : TlsChatResponse.weq Word64.concrete ByteAuth.concrete
      (Word64.concrete.band (coreDecoded state byte) (Word64.concrete.const 7)) 4 = 0 := by rw [kind]; cases wide <;> rfl
  have andZero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  change Word64.concrete.select (ByteAuth.concrete.and _ (TlsChatResponse.weq Word64.concrete ByteAuth.concrete
    (Word64.concrete.band (coreDecoded state byte) (Word64.concrete.const 7)) 3)) _
    (Word64.concrete.select (ByteAuth.concrete.and _ (TlsChatResponse.weq Word64.concrete ByteAuth.concrete
      (Word64.concrete.band (coreDecoded state byte) (Word64.concrete.const 7)) 4)) _ state.depth) = state.depth
  rw [notThree,notFour]
  simp only [andZero,Word64.select_reject]

theorem fixed_key_skip_step (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8) (wide : Bool)
    (modes : state.modes = lane 0) (terminal : VarintDecode.Spqr.terminates byte = true)
    (kind : Word64.concrete.band (coreDecoded state byte) (Word64.concrete.const 7) = Word64.concrete.const (if wide then 1 else 5)) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.skip =
      BitVec.ofNat 64 (if wide then 8 else 4) := by
  have ended : ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) = 255 := by rw [terminal_exact byte,terminal]; rfl
  change Word64.concrete.select
    (ByteAuth.concrete.and (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0)
      (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7)))
      (TlsWebSocketUpgrade.either ByteAuth.concrete
        (TlsChatResponse.weq Word64.concrete ByteAuth.concrete (Word64.concrete.band (coreDecoded state byte) (Word64.concrete.const 7)) 1)
        (TlsChatResponse.weq Word64.concrete ByteAuth.concrete (Word64.concrete.band (coreDecoded state byte) (Word64.concrete.const 7)) 5)))
    (Word64.concrete.select
      (TlsChatResponse.weq Word64.concrete ByteAuth.concrete (Word64.concrete.band (coreDecoded state byte) (Word64.concrete.const 7)) 1)
      (Word64.concrete.const 8) (Word64.concrete.const 4)) _ = _
  rw [modes,ended,kind]
  cases wide <;> exact Word64.select_accept _ _

#print axioms fixed_key_depth_step
#print axioms fixed_key_skip_step
end ChatResponseReference.StreamingUnknownV1
