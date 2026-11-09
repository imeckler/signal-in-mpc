import ChatResponseReferenceWork.StreamingV1.NativeMessageHeaderValidity
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey

private theorem zero_and (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
private theorem and_zero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
private theorem p0_off (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (modes : state.modes = lane 2) :
    TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0 = 0 := by rw [modes]; rfl
theorem message_length_kinds_step (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 2) (shape : state.kinds.length = 4) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.kinds = state.kinds := by
  change TlsWebSocketUpgrade.choose ByteAuth.concrete
    (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0) _) [_,_,_,_] state.kinds = state.kinds
  rw [p0_off state modes,zero_and,choose_reject_exact _ _ (by simpa only [List.length_cons,List.length_nil] using shape.symm)]

theorem message_length_depth_step (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 2) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.depth = state.depth := by
  change Word64.concrete.select
    (ByteAuth.concrete.and (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0) _) _) _
    (Word64.concrete.select
      (ByteAuth.concrete.and (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0) _) _) _ state.depth) = state.depth
  rw [p0_off state modes]
  simp only [zero_and,Word64.select_reject]

theorem message_length_remaining_step (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 2) (kinds : state.kinds = [0,0,255,0]) (inner : state.inner = 255) :
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

theorem message_length_inner_step (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 2) (kinds : state.kinds = [0,0,255,0]) (inner : state.inner = 255)
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

/-- Zero message length finishes immediately; every nonzero message length enters
opaque mode, so source payload bytes cannot be interpreted as padding or keys. -/
theorem message_mode_terminal (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 2) (kinds : state.kinds = [0,0,255,0])
    (terminal : VarintDecode.Spqr.terminates byte = true) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.modes =
      if coreDecoded state byte = BitVec.ofNat 64 0 then lane 0 else lane 3 := by
  have ended : ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) = 255 := by rw [terminal_exact byte,terminal]; rfl
  by_cases empty : coreDecoded state byte = BitVec.ofNat 64 0
  · rw [if_pos empty]
    have mask : TlsChatResponse.weq Word64.concrete ByteAuth.concrete (coreDecoded state byte) 0 = 255 := by
      unfold TlsChatResponse.weq; rw [word_eq_value]; exact if_pos empty
    unfold coreDecoded at mask
    simp only [TlsChatResponse.step]
    rw [modes,kinds,ended,mask]
    simp [lane,TlsWebSocketUpgrade.get,TlsWebSocketUpgrade.either,ByteAuth.concrete] <;> rfl
  · rw [if_neg empty]
    have mask : TlsChatResponse.weq Word64.concrete ByteAuth.concrete (coreDecoded state byte) 0 = 0 := by
      unfold TlsChatResponse.weq; rw [word_eq_value]; exact if_neg empty
    unfold coreDecoded at mask
    simp only [TlsChatResponse.step]
    rw [modes,kinds,ended,mask]
    simp [lane,TlsWebSocketUpgrade.get,TlsWebSocketUpgrade.either,ByteAuth.concrete] <;> rfl

#print axioms message_mode_terminal
#print axioms message_length_kinds_step
#print axioms message_length_depth_step
#print axioms message_length_remaining_step
#print axioms message_length_inner_step
end ChatResponseReference.StreamingV1
