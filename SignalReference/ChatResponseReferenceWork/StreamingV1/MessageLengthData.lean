import ChatResponseReferenceWork.StreamingV1.MessageFieldAgreement
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
private theorem and_zero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
private theorem zero_and (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
private theorem and_hot (x : BitVec 8) : ByteAuth.concrete.and 255 x = x := BitVec.allOnes_and
private theorem either_zero (x : BitVec 8) : TlsWebSocketUpgrade.either ByteAuth.concrete x 0 = x := by
  unfold TlsWebSocketUpgrade.either
  have notZero : ByteAuth.concrete.not 0 = 255 := rfl
  have rightHot (x : BitVec 8) : ByteAuth.concrete.and x 255 = x := BitVec.and_allOnes
  rw [notZero,rightHot]
  exact BitVec.not_not
private theorem either_hot (x : BitVec 8) : TlsWebSocketUpgrade.either ByteAuth.concrete x 255 = 255 := by
  unfold TlsWebSocketUpgrade.either
  have notHot : ByteAuth.concrete.not 255 = 0 := rfl
  rw [notHot,and_zero]
  rfl

theorem message_length_response_data (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 2) (kinds : state.kinds = [0,0,255,0])
    (terminal : VarintDecode.Spqr.terminates byte = true) :
    responseData (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state =
      {responseData state with messagePresent := 255} := by
  have ended : ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) = 255 := by rw [terminal_exact byte,terminal]; rfl
  simp only [responseData,TlsChatResponse.step]
  rw [modes,kinds,ended]
  have p0 : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 2) 0 = 0 := rfl
  have p1 : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 2) 1 = 0 := rfl
  have p2 : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 2) 2 = 255 := rfl
  have k1 : TlsWebSocketUpgrade.get ByteAuth.concrete [0,0,255,0] 1 = 0 := rfl
  have k2 : TlsWebSocketUpgrade.get ByteAuth.concrete [0,0,255,0] 2 = 255 := rfl
  simp only [p0,p1,p2,k1,k2,zero_and,and_hot,and_zero,Word64.select_reject,Word64.select_accept,either_zero,either_hot]

#print axioms message_length_response_data
end ChatResponseReference.StreamingV1
