import ChatResponseReferenceWork.StreamingV1.BodyFieldComplete
import ChatResponseReferenceWork.Utf8Machine
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1

/-- Exact UTF state advancement for actual message/header payload bytes, even
when another guard already rejected the record. No UTF8 validity is assumed. -/
theorem string_utf_step (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 3)
    (stringKind : TlsWebSocketUpgrade.either ByteAuth.concrete
      (TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 2)
      (TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 3) = 255)
    (shape : state.utf.length = 8) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.utf =
      TlsWebSocketFrame.utfStep ByteAuth.concrete state.utf byte := by
  change TlsWebSocketUpgrade.choose ByteAuth.concrete
    (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 2) _) _
    (TlsWebSocketUpgrade.choose ByteAuth.concrete
      (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 3)
        (TlsWebSocketUpgrade.either ByteAuth.concrete
          (TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 2)
          (TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 3))) _ state.utf) = _
  rw [modes,stringKind]
  have off : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 3) 2 = 0 := rfl
  have on : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 3) 3 = 255 := rfl
  have zeroAnd (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  have hot : ByteAuth.concrete.and 255 255 = 255 := rfl
  rw [off,on,zeroAnd,hot]
  rw [choose_accept_exact _ _ (by change 8 = state.utf.length; exact shape.symm)]
  exact choose_reject_exact _ _ rfl

/-- Actual String length completion resets UTF validation, including empty and
duplicate fields. This reset occurs independently of the valid output mask. -/
theorem string_utf_reset (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 2) (terminal : VarintDecode.Spqr.terminates byte = true)
    (shape : state.utf.length = 8) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.utf = Utf8.encode .ready := by
  have ended : ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) = 255 := by rw [terminal_exact byte,terminal]; rfl
  change TlsWebSocketUpgrade.choose ByteAuth.concrete
    (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 2)
      (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7))) _ _ = _
  rw [modes,ended]
  have on : ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete (lane 2) 2) 255 = 255 := rfl
  rw [on,choose_accept_exact _ _ (by
    simp only [TlsWebSocketUpgrade.choose,List.length_zipWith]
    have nextShape : (TlsWebSocketFrame.utfStep ByteAuth.concrete state.utf byte).length = 8 := rfl
    rw [nextShape,shape]; rfl)]
  rfl

#print axioms string_utf_step
#print axioms string_utf_reset
end ChatResponseReference.StreamingV1
