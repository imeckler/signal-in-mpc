import ChatResponseReferenceWork.StreamingV1.OpaquePrefix
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 1000000

/-- The native field-kind classification survives each continuing length byte. -/
theorem nonterminal_kinds (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (continues : VarintDecode.Spqr.terminates byte = false) (shape : state.kinds.length = 4) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.kinds = state.kinds := by
  have ended : ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) = 0 := by rw [terminal_exact byte,continues]; rfl
  change TlsWebSocketUpgrade.choose ByteAuth.concrete
    (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0)
      (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7))) [_,_,_,_] state.kinds = state.kinds
  rw [ended]
  have andZero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  rw [andZero,choose_reject_exact _ _ (by simpa only [List.length_cons,List.length_nil] using shape.symm)]

theorem prefix_kinds (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (leading : List (BitVec 8))
    (continues : ∀ byte ∈ leading, VarintDecode.Spqr.terminates byte = false) (shape : state.kinds.length = 4) :
    (feed state leading).kinds = state.kinds := by
  induction leading generalizing state with
  | nil => rfl
  | cons byte rest ih =>
    have first := continues byte (by simp)
    have result := ih _ (by intro x member; exact continues x (by simp [member])) (key_kinds_shape state byte shape)
    exact result.trans (nonterminal_kinds state byte first shape)

private theorem body_reset_on (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 2) (kinds : state.kinds = [0,255,0,0])
    (terminal : VarintDecode.Spqr.terminates byte = true) :
    ByteAuth.concrete.and
      (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 2)
        (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7)))
      (TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 1) = 255 := by
  rw [modes,kinds,terminal_exact byte,terminal]
  rfl

/-- Actual body length replacement and reset, including zero-length duplicates. -/
theorem body_length_terminal (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 2) (kinds : state.kinds = [0,255,0,0])
    (terminal : VarintDecode.Spqr.terminates byte = true) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.bodyLength = coreDecoded state byte := by
  change Word64.concrete.select
    (ByteAuth.concrete.and
      (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 2)
        (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7)))
      (TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 1)) (coreDecoded state byte) state.bodyLength = _
  rw [body_reset_on state byte modes kinds terminal]
  exact Word64.select_accept _ _

theorem body_present_terminal (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 2) (kinds : state.kinds = [0,255,0,0])
    (terminal : VarintDecode.Spqr.terminates byte = true) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.bodyPresent = 255 := by
  change TlsWebSocketUpgrade.either ByteAuth.concrete state.bodyPresent
    (ByteAuth.concrete.and
      (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 2)
        (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7)))
      (TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 1)) = 255
  rw [body_reset_on state byte modes kinds terminal]
  unfold TlsWebSocketUpgrade.either
  have notHot : ByteAuth.concrete.not 255 = 0 := rfl
  have andZero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  rw [notHot,andZero]
  rfl

/-- Body reset is visible under exactly the actual next-valid mask. -/
theorem body_reset_event (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 2) (kinds : state.kinds = [0,255,0,0])
    (terminal : VarintDecode.Spqr.terminates byte = true) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).bodyReset =
      (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.valid := by
  change ByteAuth.concrete.and _
    (ByteAuth.concrete.and
      (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 2)
        (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7)))
      (TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 1)) = _
  rw [body_reset_on state byte modes kinds terminal]
  have hot (x : BitVec 8) : ByteAuth.concrete.and x 255 = x := BitVec.and_allOnes
  exact hot _

/-- Actual decoded length installs the exact opaque byte counter. -/
theorem length_skip_terminal (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 2) (terminal : VarintDecode.Spqr.terminates byte = true) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.skip = coreDecoded state byte := by
  have ended : ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) = 255 := by rw [terminal_exact byte,terminal]; rfl
  change Word64.concrete.select
    (ByteAuth.concrete.and
      (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0)
        (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7))) _) _
    (Word64.concrete.select
      (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 2)
        (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7))) (coreDecoded state byte) _) = _
  rw [modes,ended]
  have keyOff : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 2) 0 = 0 := rfl
  have lengthOn : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 2) 2 = 255 := rfl
  have zeroAnd (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  have hot : ByteAuth.concrete.and 255 255 = 255 := rfl
  rw [keyOff,lengthOn]
  simp only [zeroAnd,hot,Word64.select_reject,Word64.select_accept]

/-- Zero body length finishes immediately; every nonzero body length enters
opaque mode, so source payload bytes cannot be interpreted as padding or keys. -/
theorem body_mode_terminal (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 2) (kinds : state.kinds = [0,255,0,0])
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

#print axioms nonterminal_kinds
#print axioms prefix_kinds
#print axioms body_length_terminal
#print axioms body_present_terminal
#print axioms body_reset_event
#print axioms length_skip_terminal
#print axioms body_mode_terminal
end ChatResponseReference.StreamingV1
