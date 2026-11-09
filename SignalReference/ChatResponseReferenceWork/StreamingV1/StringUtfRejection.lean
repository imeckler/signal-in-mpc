import ChatResponseReferenceWork.StreamingV1.StringUtfPrefix
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1

/-- A String payload ending outside UTF ready rejects the actual Core byte
transition, whether malformed or merely truncated, for message and header kinds. -/
theorem string_utf_terminal_reject (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 3) (last : state.skip = BitVec.ofNat 64 1)
    (stringKind : TlsWebSocketUpgrade.either ByteAuth.concrete
      (TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 2)
      (TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 3) = 255)
    (bad : TlsWebSocketUpgrade.get ByteAuth.concrete (TlsWebSocketFrame.utfStep ByteAuth.concrete state.utf byte) 0 = 0) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.valid = 0 := by
  have p3 : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 3) 3 = 255 := rfl
  have lastMask : TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.skip 1 = 255 := by rw [last]; rfl
  have zeroAnd (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  have andZero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  have hot : ByteAuth.concrete.and 255 255 = 255 := rfl
  have notZero : ByteAuth.concrete.not 0 = 255 := rfl
  have notHot : ByteAuth.concrete.not 255 = 0 := rfl
  simp only [TlsChatResponse.step]
  rw [bad,lastMask,modes]
  simp only [p3,stringKind,hot,zeroAnd,andZero,notZero,notHot]

#print axioms string_utf_terminal_reject
end ChatResponseReference.StreamingV1
