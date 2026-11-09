import ChatResponseReferenceWork.StreamingV1.OpaqueControls
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey
/-- Zero body length finishes immediately; every nonzero body length enters
opaque mode, so source payload bytes cannot be interpreted as padding or keys. -/
theorem nonresponse_length_mode_terminal (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 2) (kindsOff : TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 0 = 0)
    (terminal : VarintDecode.Spqr.terminates byte = true) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.modes =
      if coreDecoded state byte = BitVec.ofNat 64 0 then lane 0 else lane 3 := by
  have ended : ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) = 255 := by rw [terminal_exact byte,terminal]; rfl
  by_cases empty : coreDecoded state byte = BitVec.ofNat 64 0
  · rw [if_pos empty]
    have mask : TlsChatResponse.weq Word64.concrete ByteAuth.concrete (coreDecoded state byte) 0 = 255 := by
      unfold TlsChatResponse.weq; rw [word_eq_value]; exact if_pos empty
    unfold coreDecoded at mask
    simp only [TlsChatResponse.step]
    rw [modes,ended,mask,kindsOff]
    simp [lane,TlsWebSocketUpgrade.get,TlsWebSocketUpgrade.either,ByteAuth.concrete] <;> rfl
  · rw [if_neg empty]
    have mask : TlsChatResponse.weq Word64.concrete ByteAuth.concrete (coreDecoded state byte) 0 = 0 := by
      unfold TlsChatResponse.weq; rw [word_eq_value]; exact if_neg empty
    unfold coreDecoded at mask
    simp only [TlsChatResponse.step]
    rw [modes,ended,mask,kindsOff]
    simp [lane,TlsWebSocketUpgrade.get,TlsWebSocketUpgrade.either,ByteAuth.concrete] <;> rfl

#print axioms nonresponse_length_mode_terminal
end ChatResponseReference.StreamingV1
