import ChatResponseReferenceWork.StreamingV1.ScalarPayload
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
set_option maxHeartbeats 1000000

theorem scalar_continue_tag (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (byte : BitVec 8) (modes : state.modes = lane 1) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.tag = state.tag := by
  change Word64.concrete.select
    (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0) _) _ state.tag = state.tag
  rw [modes]
  change Word64.concrete.select (ByteAuth.concrete.and 0 _) _ state.tag = state.tag
  have zero (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  rw [zero]
  exact Word64.select_reject _ _

theorem scalar_continue_known (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (byte : BitVec 8) (modes : state.modes = lane 1) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.scalarKnown = state.scalarKnown := by
  change TlsInner.select ByteAuth.concrete
    (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0) _) _ state.scalarKnown = state.scalarKnown
  rw [modes]
  change TlsInner.select ByteAuth.concrete (ByteAuth.concrete.and 0 _) _ state.scalarKnown = state.scalarKnown
  have zero (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  rw [zero]
  exact TlsInner.select_reject _ _

/-- A scalar prefix cannot close its response before the explicit remaining
counter reaches one. This is independent of other accumulated field values. -/
theorem scalar_continue_inner (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (byte : BitVec 8) (modes : state.modes = lane 1) (inner : state.inner = 255)
    (remaining : TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.responseRemaining 1 = 0) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.inner = 255 := by
  change TlsInner.select ByteAuth.concrete
    (ByteAuth.concrete.and
      (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 2) _)
      (TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 0)) _
    (TlsInner.select ByteAuth.concrete
      (ByteAuth.concrete.and state.inner (TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.responseRemaining 1)) 0 state.inner) = 255
  rw [modes,inner,remaining]
  have zero (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  have hotZero : ByteAuth.concrete.and 255 0 = 0 := rfl
  have laneTwo : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 1) 2 = 0 := rfl
  rw [hotZero,laneTwo,zero,zero,TlsInner.select_reject,TlsInner.select_reject]

/-- The actual counter decrements once per scalar-prefix byte. -/
theorem scalar_continue_remaining (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (byte : BitVec 8) (modes : state.modes = lane 1) (inner : state.inner = 255) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.responseRemaining =
      Word64.concrete.sub state.responseRemaining 1 := by
  change Word64.concrete.select
    (ByteAuth.concrete.and
      (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 2) _)
      (TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 0)) _
    (Word64.concrete.select state.inner (Word64.concrete.sub state.responseRemaining 1) state.responseRemaining) = _
  rw [modes,inner]
  have zero (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  have laneTwo : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 1) 2 = 0 := rfl
  rw [laneTwo,zero,zero,Word64.select_reject,Word64.select_accept]

#print axioms scalar_continue_tag
#print axioms scalar_continue_known
#print axioms scalar_continue_inner
#print axioms scalar_continue_remaining
end ChatResponseReference.StreamingV1
