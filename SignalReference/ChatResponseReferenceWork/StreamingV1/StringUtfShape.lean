import ChatResponseReferenceWork.StreamingV1.MessageLengthContext
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1

theorem step_utf_shape (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (shape : state.utf.length = 8) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.utf.length = 8 := by
  change (TlsWebSocketUpgrade.choose ByteAuth.concrete _ (TlsWebSocketUpgrade.initial ByteAuth.concrete 7)
    (TlsWebSocketUpgrade.choose ByteAuth.concrete _ (TlsWebSocketFrame.utfStep ByteAuth.concrete state.utf byte) state.utf)).length = 8
  have utfLength : (TlsWebSocketFrame.utfStep ByteAuth.concrete state.utf byte).length = 8 := rfl
  simp only [TlsWebSocketUpgrade.choose,TlsWebSocketUpgrade.initial,List.length_zipWith,
    List.length_cons,List.length_replicate,utfLength,shape]
  rfl

theorem feed_utf_shape (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (bytes : List (BitVec 8))
    (shape : state.utf.length = 8) : (feed state bytes).utf.length = 8 := by
  induction bytes generalizing state with
  | nil => exact shape
  | cons byte rest ih => exact ih _ (step_utf_shape state byte shape)

#print axioms step_utf_shape
#print axioms feed_utf_shape
end ChatResponseReference.StreamingV1
