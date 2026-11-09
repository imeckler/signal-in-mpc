import ChatResponseReferenceWork.StreamingUnknownV1.GroupKeyEntry
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

private theorem zero_and (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
private theorem and_zero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
private theorem hot_and (x : BitVec 8) : ByteAuth.concrete.and 255 x = x := BitVec.allOnes_and
private theorem not_zero : ByteAuth.concrete.not 0 = 255 := rfl
private theorem not_hot : ByteAuth.concrete.not 255 = 0 := rfl
private theorem either_zero : TlsWebSocketUpgrade.either ByteAuth.concrete 0 0 = 0 := rfl

private theorem position_live (group : Nat) (bound : group < 10) :
    TlsWebSocketUpgrade.any ByteAuth.concrete (oneHot group) = 255 := by
  have cases : group = 0 ∨ group = 1 ∨ group = 2 ∨ group = 3 ∨ group = 4 ∨ group = 5 ∨ group = 6 ∨ group = 7 ∨ group = 8 ∨ group = 9 := by omega
  rcases cases with h|h|h|h|h|h|h|h|h|h <;> subst group <;> rfl
private theorem position_not_tenth (group : Nat) (bound : group < 9) :
    TlsWebSocketUpgrade.get ByteAuth.concrete (oneHot group) 9 = 0 := by
  have cases : group = 0 ∨ group = 1 ∨ group = 2 ∨ group = 3 ∨ group = 4 ∨ group = 5 ∨ group = 6 ∨ group = 7 ∨ group = 8 := by omega
  rcases cases with h|h|h|h|h|h|h|h|h <;> subst group <;> rfl

/-- A matching outermost group end terminal preserves validity, including exact
private child closure. Actual guard acceptance is supplied by the separately
proved native/active-parent guard relation. -/
theorem group_end_terminal_valid (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (byte : BitVec 8) (group : Nat) (bound : group < 10)
    (modes : state.modes = lane 0) (positions : state.positions = oneHot group)
    (valid : state.valid = 255) (seen : state.seen = 255) (finished : state.finished = 0)
    (budget : TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.budget 0 = 0)
    (depth : state.depth = 1)
    (kind : Word64.concrete.band (coreDecoded state byte) (Word64.concrete.const 7) = Word64.concrete.const 4)
    (keyGood : actualKeyGood state byte = 255)
 (terminal : VarintDecode.Spqr.terminates byte = true)
    (tenth : group = 9 → byte.toNat < 2) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.valid = 255 := by
  have ended : ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) = 255 := by rw [terminal_exact byte,terminal]; rfl
  have p0 : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 0) 0 = 255 := rfl
  have p1 : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 0) 1 = 0 := rfl
  have p2 : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 0) 2 = 0 := rfl
  have p3 : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 0) 3 = 0 := rfl
  have live : TlsWebSocketUpgrade.any ByteAuth.concrete state.positions = 255 := by rw [positions]; exact position_live group bound
  have overflow : ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.positions 9)
      (ByteAuth.concrete.not (TlsWebSocketUpgrade.eq ByteAuth.concrete
        (ByteAuth.concrete.and byte (ByteAuth.concrete.const 254)) 0)) = 0 := by
    rw [positions,final_overflow_exact byte]
    by_cases last : group = 9
    · subst group
      rw [if_pos (tenth rfl)]
      rfl
    · rw [position_not_tenth group (by omega)]
      exact zero_and _
  have rightHot (x : BitVec 8) : ByteAuth.concrete.and x 255 = x := BitVec.and_allOnes
  have fixedOff : TlsWebSocketUpgrade.either ByteAuth.concrete
      (TlsChatResponse.weq Word64.concrete ByteAuth.concrete (Word64.concrete.band (coreDecoded state byte) (Word64.concrete.const 7)) 1)
      (TlsChatResponse.weq Word64.concrete ByteAuth.concrete (Word64.concrete.band (coreDecoded state byte) (Word64.concrete.const 7)) 5) = 0 := by rw [kind]; rfl
  unfold coreDecoded at fixedOff kind
  have k3 : TlsChatResponse.weq Word64.concrete ByteAuth.concrete (Word64.concrete.const 4) 3 = 0 := rfl
  have k4 : TlsChatResponse.weq Word64.concrete ByteAuth.concrete (Word64.concrete.const 4) 4 = 255 := rfl
  have oneDown : Word64.concrete.sub 1 (Word64.concrete.const 1) = 0 := rfl
  have zeroEq : TlsChatResponse.weq Word64.concrete ByteAuth.concrete 0 0 = 255 := rfl
  simp only [TlsChatResponse.step]
  change ByteAuth.concrete.and state.valid
    (ByteAuth.concrete.and state.seen (ByteAuth.concrete.and (ByteAuth.concrete.not state.finished)
      (ByteAuth.concrete.and _ (ByteAuth.concrete.and _
        (ByteAuth.concrete.and
          (ByteAuth.concrete.not (ByteAuth.concrete.and
            (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0)
              (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7)))
            (ByteAuth.concrete.not (actualKeyGood state byte)))) _))))) = 255
  rw [keyGood,valid,seen,finished,modes,ended,budget,live,overflow,fixedOff]
  simp only [p0,p1,p2,p3,zero_and,and_zero,hot_and,rightHot,not_zero,not_hot,either_zero,Word64.select_reject]
  rw [kind,depth]
  simp only [k3,k4,zero_and,and_zero,hot_and,rightHot,not_zero,not_hot,either_zero,Word64.select_reject,Word64.select_accept,oneDown,zeroEq]

  change ByteAuth.concrete.not (ByteAuth.concrete.and _ (ByteAuth.concrete.not 255)) = 255
  rw [not_hot,and_zero,not_zero]

#print axioms group_end_terminal_valid
end ChatResponseReference.StreamingUnknownV1
