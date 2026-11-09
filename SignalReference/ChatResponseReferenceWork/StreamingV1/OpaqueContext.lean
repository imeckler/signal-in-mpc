import ChatResponseReferenceWork.StreamingV1.OpaqueValidity
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1

private theorem zero_and (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
private theorem and_zero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
private theorem p0_off (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (modes : state.modes = lane 3) :
    TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0 = 0 := by rw [modes]; rfl
private theorem p2_off (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (modes : state.modes = lane 3) :
    TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 2 = 0 := by rw [modes]; rfl

theorem opaque_kinds_step (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 3) (shape : state.kinds.length = 4) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.kinds = state.kinds := by
  change TlsWebSocketUpgrade.choose ByteAuth.concrete
    (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0) _) [_,_,_,_] state.kinds = state.kinds
  rw [p0_off state modes,zero_and,choose_reject_exact _ _ (by simpa only [List.length_cons,List.length_nil] using shape.symm)]

theorem opaque_depth_step (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 3) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.depth = state.depth := by
  change Word64.concrete.select
    (ByteAuth.concrete.and (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0) _) _) _
    (Word64.concrete.select
      (ByteAuth.concrete.and (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0) _) _) _ state.depth) = state.depth
  rw [p0_off state modes]
  simp only [zero_and,Word64.select_reject]

theorem opaque_remaining_step (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 3) (inner : state.inner = 255) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.responseRemaining =
      Word64.concrete.sub state.responseRemaining 1 := by
  change Word64.concrete.select
    (ByteAuth.concrete.and (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 2) _) _) _
    (Word64.concrete.select state.inner (Word64.concrete.sub state.responseRemaining 1) state.responseRemaining) = _
  rw [p2_off state modes,inner]
  simp only [zero_and,Word64.select_reject,Word64.select_accept]

theorem opaque_inner_step (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 3) (inner : state.inner = 255)
    (notClosing : TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.responseRemaining 1 = 0) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.inner = 255 := by
  change TlsInner.select ByteAuth.concrete
    (ByteAuth.concrete.and (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 2) _) _) _
    (TlsInner.select ByteAuth.concrete
      (ByteAuth.concrete.and state.inner (TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.responseRemaining 1)) 0 state.inner) = 255
  rw [p2_off state modes,inner,notClosing]
  simp only [zero_and,and_zero,TlsInner.select_reject]

#print axioms opaque_kinds_step
#print axioms opaque_depth_step
#print axioms opaque_remaining_step
#print axioms opaque_inner_step
end ChatResponseReference.StreamingV1
