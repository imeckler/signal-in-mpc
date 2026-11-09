import ChatResponseReferenceWork.StreamingV1.NativeScalarValidity
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1

private theorem zero_and (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
private theorem and_zero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
private theorem hot_and (x : BitVec 8) : ByteAuth.concrete.and 255 x = x := BitVec.allOnes_and
private theorem not_hot : ByteAuth.concrete.not 255 = 0 := rfl
private theorem not_zero : ByteAuth.concrete.not 0 = 255 := rfl
private theorem either_zero (x : BitVec 8) : TlsWebSocketUpgrade.either ByteAuth.concrete x 0 = x := by
  unfold TlsWebSocketUpgrade.either
  have rightHot (x : BitVec 8) : ByteAuth.concrete.and x 255 = x := BitVec.and_allOnes
  rw [not_zero,rightHot]
  exact BitVec.not_not
private theorem either_hot (x : BitVec 8) : TlsWebSocketUpgrade.either ByteAuth.concrete x 255 = 255 := by
  unfold TlsWebSocketUpgrade.either
  rw [not_hot,and_zero]
  rfl

theorem id_terminal_response_data (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 1) (known : state.scalarKnown = 255) (inner : state.inner = 255)
    (tag : state.tag = 1) (terminal : VarintDecode.Spqr.terminates byte = true) :
    responseData (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state =
      {responseData state with idPresent := 255,id := coreDecoded state byte} := by
  have ended : ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) = 255 := by rw [terminal_exact byte,terminal]; rfl
  simp only [responseData,TlsChatResponse.step]
  rw [modes,known,inner,tag,ended]
  have p0 : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 1) 0 = 0 := rfl
  have p1 : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 1) 1 = 255 := rfl
  have p2 : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 1) 2 = 0 := rfl
  have same : TlsChatResponse.weq Word64.concrete ByteAuth.concrete 1 1 = 255 := rfl
  have other : TlsChatResponse.weq Word64.concrete ByteAuth.concrete 1 2 = 0 := rfl
  simp only [p0,p1,p2,same,other,zero_and,and_zero,hot_and,not_hot,either_zero,either_hot,
    Word64.select_reject,Word64.select_accept]
  rfl

theorem status_terminal_response_data (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 1) (known : state.scalarKnown = 255) (inner : state.inner = 255)
    (tag : state.tag = 2) (terminal : VarintDecode.Spqr.terminates byte = true) :
    responseData (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state =
      {responseData state with status := Word64.concrete.band (coreDecoded state byte) (Word64.concrete.const 4294967295)} := by
  have ended : ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) = 255 := by rw [terminal_exact byte,terminal]; rfl
  simp only [responseData,TlsChatResponse.step]
  rw [modes,known,inner,tag,ended]
  have p0 : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 1) 0 = 0 := rfl
  have p1 : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 1) 1 = 255 := rfl
  have p2 : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 1) 2 = 0 := rfl
  have same : TlsChatResponse.weq Word64.concrete ByteAuth.concrete 2 2 = 255 := rfl
  have other : TlsChatResponse.weq Word64.concrete ByteAuth.concrete 2 1 = 0 := rfl
  simp only [p0,p1,p2,same,other,zero_and,and_zero,hot_and,not_hot,either_zero,either_hot,
    Word64.select_reject,Word64.select_accept]
  rfl

theorem scalar_terminal_modes (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 1) (terminal : VarintDecode.Spqr.terminates byte = true) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.modes = lane 0 := by
  have ended : ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) = 255 := by rw [terminal_exact byte,terminal]; rfl
  simp only [TlsChatResponse.step]
  rw [modes,ended]
  simp [lane,TlsWebSocketUpgrade.get,TlsWebSocketUpgrade.either,ByteAuth.concrete] <;> rfl

#print axioms id_terminal_response_data
#print axioms status_terminal_response_data
#print axioms scalar_terminal_modes
end ChatResponseReference.StreamingV1
