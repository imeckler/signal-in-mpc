import ChatResponseReferenceWork.StreamingV1.KeyScopeStep
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

theorem inner_key_response_data (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 0) (inner : state.inner = 255) :
    responseData (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state = responseData state := by
  simp only [responseData,TlsChatResponse.step]
  rw [modes,inner]
  have p1 : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 0) 1 = 0 := rfl
  have p2 : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 0) 2 = 0 := rfl
  have notHot : ByteAuth.concrete.not 255 = 0 := rfl
  simp only [p1,p2,notHot,zero_and,and_zero,Word64.select_reject,either_zero]
  simp only [TlsWebSocketUpgrade.get,List.getElem?_cons_zero,Option.getD_some,and_zero,either_zero]

#print axioms inner_key_response_data
end ChatResponseReference.StreamingV1
