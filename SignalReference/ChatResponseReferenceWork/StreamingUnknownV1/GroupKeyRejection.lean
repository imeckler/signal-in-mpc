import ChatResponseReferenceWork.StreamingUnknownV1.GroupEndActive
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1

/-- Failed actual key guard forces rejection regardless of the other state;
stack/depth/data mutation of that step remains represented by the actual step. -/
theorem actual_key_guard_reject (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 0) (terminal : VarintDecode.Spqr.terminates byte = true)
    (invalid : actualKeyGood state byte = 0) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.valid = 0 := by
  have ended : ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) = 255 := by rw [terminal_exact byte,terminal]; rfl
  change ByteAuth.concrete.and state.valid
    (ByteAuth.concrete.and state.seen (ByteAuth.concrete.and (ByteAuth.concrete.not state.finished)
      (ByteAuth.concrete.and _ (ByteAuth.concrete.and _
        (ByteAuth.concrete.and
          (ByteAuth.concrete.not (ByteAuth.concrete.and
            (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0)
              (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7)))
            (ByteAuth.concrete.not (actualKeyGood state byte)))) _))))) = 0
  rw [invalid,modes,ended]
  have killed : ByteAuth.concrete.not (ByteAuth.concrete.and
      (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete (lane 0) 0) 255)
      (ByteAuth.concrete.not 0)) = 0 := rfl
  rw [killed]
  have zeroAnd (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  have andZero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  simp only [zeroAnd,andZero]

#print axioms actual_key_guard_reject
end ChatResponseReference.StreamingUnknownV1
