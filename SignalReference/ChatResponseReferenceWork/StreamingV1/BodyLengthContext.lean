import ChatResponseReferenceWork.StreamingV1.NativeBodyHeaderValidity
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1

private theorem zero_and (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
private theorem and_zero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
private theorem p0_off (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (modes : state.modes = lane 2) :
    TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0 = 0 := by rw [modes]; rfl
theorem body_length_kinds_step (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 2) (shape : state.kinds.length = 4) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.kinds = state.kinds := by
  change TlsWebSocketUpgrade.choose ByteAuth.concrete
    (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0) _) [_,_,_,_] state.kinds = state.kinds
  rw [p0_off state modes,zero_and,choose_reject_exact _ _ (by simpa only [List.length_cons,List.length_nil] using shape.symm)]

theorem body_length_depth_step (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 2) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.depth = state.depth := by
  change Word64.concrete.select
    (ByteAuth.concrete.and (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0) _) _) _
    (Word64.concrete.select
      (ByteAuth.concrete.and (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0) _) _) _ state.depth) = state.depth
  rw [p0_off state modes]
  simp only [zero_and,Word64.select_reject]

theorem body_length_remaining_step (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 2) (kinds : state.kinds = [0,255,0,0]) (inner : state.inner = 255) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.responseRemaining =
      Word64.concrete.sub state.responseRemaining 1 := by
  change Word64.concrete.select
    (ByteAuth.concrete.and (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 2) _) _) _
    (Word64.concrete.select state.inner (Word64.concrete.sub state.responseRemaining 1) state.responseRemaining) = _
  have enterOff : ByteAuth.concrete.and
      (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 2)
        (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7)))
      (TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 0) = 0 := by
    rw [kinds]; exact and_zero _
  rw [enterOff,inner]
  simp only [zero_and,Word64.select_reject,Word64.select_accept]

theorem body_length_inner_step (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 2) (kinds : state.kinds = [0,255,0,0]) (inner : state.inner = 255)
    (notClosing : TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.responseRemaining 1 = 0) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.inner = 255 := by
  change TlsInner.select ByteAuth.concrete
    (ByteAuth.concrete.and (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 2) _) _) _
    (TlsInner.select ByteAuth.concrete
      (ByteAuth.concrete.and state.inner (TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.responseRemaining 1)) 0 state.inner) = 255
  have enterOff : ByteAuth.concrete.and
      (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 2)
        (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7)))
      (TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 0) = 0 := by
    rw [kinds]; exact and_zero _
  rw [enterOff,inner,notClosing]
  simp only [zero_and,and_zero,TlsInner.select_reject]

#print axioms body_length_kinds_step
#print axioms body_length_depth_step
#print axioms body_length_remaining_step
#print axioms body_length_inner_step
end ChatResponseReference.StreamingV1
