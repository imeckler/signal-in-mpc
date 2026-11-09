import ChatResponseReferenceWork.StreamingUnknownV1.GroupKeyGuard
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1

/-- Nested keys cannot install scalar/body/message/header schema masks, even
when their numeric tag coincides with a real response field. -/
theorem nested_key_scalar_off (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 0)
    (notTop : TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.depth 0 = 0)
    (terminal : VarintDecode.Spqr.terminates byte = true) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.scalarKnown = 0 := by
  have ended : ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) = 255 := by rw [terminal_exact byte,terminal]; rfl
  change TlsInner.select ByteAuth.concrete
    (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0) (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7)))
    (scalarKeyMask state byte) state.scalarKnown = 0
  rw [(nested_schema_masks state byte notTop).1,modes,ended]
  exact TlsInner.select_accept _ _

theorem nested_key_kinds_off (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 0) (shape : state.kinds.length = 4)
    (notTop : TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.depth 0 = 0)
    (terminal : VarintDecode.Spqr.terminates byte = true) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.kinds = [0,0,0,0] := by
  have ended : ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) = 255 := by rw [terminal_exact byte,terminal]; rfl
  change TlsWebSocketUpgrade.choose ByteAuth.concrete
    (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0) (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7)))
    [ByteAuth.concrete.and (TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.depth 0) _,
     ByteAuth.concrete.and (TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.depth 0) _,
     ByteAuth.concrete.and (TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.depth 0) _,
     ByteAuth.concrete.and (TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.depth 0) _] state.kinds = _
  have zeroAnd (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  rw [notTop,modes,ended]
  simp only [zeroAnd]
  exact choose_accept_exact _ _ (by simpa only [List.length_cons,List.length_nil] using shape.symm)

#print axioms nested_key_scalar_off
#print axioms nested_key_kinds_off
end ChatResponseReference.StreamingUnknownV1
