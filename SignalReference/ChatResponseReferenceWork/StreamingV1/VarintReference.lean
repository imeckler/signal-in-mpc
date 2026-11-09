import ChatResponseReferenceWork.ByteMasks
import ChatResponseReferenceWork.OuterEnvelopeV1.ScalarReference
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def oneHot (index : Nat) : List (BitVec 8) :=
  (List.range 10).map (fun i => if i = index then 255 else 0)

theorem position_initial : TlsWebSocketUpgrade.initial ByteAuth.concrete 9 = oneHot 0 := rfl

theorem position_advance (index : Nat) (bound : index < 9) :
    (0 : BitVec 8) :: (oneHot index).take 9 = oneHot (index+1) := by
  have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 := by omega
  rcases cases with h|h|h|h|h|h|h|h|h <;> subst index <;> rfl

/-- Exact numeric contribution used by the actual Core step, for all ten varint
positions and all byte values. This includes permissive payload truncation at
position9; the independent strict Prost overflow guard is proved below. -/
theorem contribution_one_hot (index : Nat) (bound : index < 10) : ∀ byte : BitVec 8,
    TlsChatResponse.contribution VarintDecode.Spqr.concrete ByteAuth.concrete (oneHot index) byte =
      VarintDecode.Spqr.payload byte index := by
  have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 := by omega
  rcases cases with h|h|h|h|h|h|h|h|h|h <;> subst index <;> decide +kernel

theorem terminal_exact : ∀ byte : BitVec 8,
    ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) =
      if VarintDecode.Spqr.terminates byte then 255 else 0 := by decide +kernel

/-- The Core guard is stricter than the permissive SPQR value accumulator:
position9 accepts only byte0/1, exactly as pinned Prost's full reference. -/
theorem final_overflow_exact : ∀ byte : BitVec 8,
    ByteAuth.concrete.not (TlsWebSocketUpgrade.eq ByteAuth.concrete
      (ByteAuth.concrete.and byte (ByteAuth.concrete.const 254)) 0) =
      if byte.toNat < 2 then 0 else 255 := by decide +kernel

/-- Actual scalar-ID assignment at a terminating byte, without a parse-validity
premise. Invalid varints may update internal data, but their validity guard is
separate and never converts an error into success. -/
theorem core_id_terminal (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (index : Nat) (bound : index < 10) (byte : BitVec 8)
    (modes : state.modes = [0,255,0,0]) (positions : state.positions = oneHot index)
    (known : state.scalarKnown = 255) (inner : state.inner = 255) (tag : state.tag = 1)
    (terminal : VarintDecode.Spqr.terminates byte = true) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.id =
      state.value ||| VarintDecode.Spqr.payload byte index := by
  change Word64.concrete.select
    (ByteAuth.concrete.and
      (ByteAuth.concrete.and
        (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 1)
          (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7))) state.scalarKnown)
      (ByteAuth.concrete.and state.inner (TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.tag 1)))
    (VarintDecode.Spqr.concrete.orWord state.value
      (TlsChatResponse.contribution VarintDecode.Spqr.concrete ByteAuth.concrete state.positions byte)) state.id = _
  have tagMask : TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.tag 1 = 255 := by
    rw [tag]
    change Word64.eq Word64.concrete ByteAuth.concrete (1 : BitVec 64) 1 = 255
    unfold Word64.eq
    rw [ByteAuth.equalMask_value]
    simp
  rw [positions,contribution_one_hot index bound byte,terminal_exact byte,terminal,tagMask,modes,known,inner]
  change Word64.concrete.select 255 (state.value ||| VarintDecode.Spqr.payload byte index) state.id = _
  exact Word64.select_accept _ _
theorem core_status_terminal (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (index : Nat) (bound : index < 10) (byte : BitVec 8)
    (modes : state.modes = [0,255,0,0]) (positions : state.positions = oneHot index)
    (known : state.scalarKnown = 255) (inner : state.inner = 255) (tag : state.tag = 2)
    (terminal : VarintDecode.Spqr.terminates byte = true) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.status =
      (state.value ||| VarintDecode.Spqr.payload byte index) &&& 4294967295 := by
  change Word64.concrete.select
    (ByteAuth.concrete.and
      (ByteAuth.concrete.and
        (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 1)
          (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7))) state.scalarKnown)
      (ByteAuth.concrete.and (state.inner) (TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.tag 2)))
    (Word64.concrete.band
      (VarintDecode.Spqr.concrete.orWord state.value
        (TlsChatResponse.contribution VarintDecode.Spqr.concrete ByteAuth.concrete state.positions byte))
      (Word64.concrete.const 4294967295)) state.status = _
  have tagMask : TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.tag 2 = 255 := by
    rw [tag]
    change Word64.eq Word64.concrete ByteAuth.concrete (2 : BitVec 64) 2 = 255
    unfold Word64.eq
    rw [ByteAuth.equalMask_value]
    simp
  rw [positions,contribution_one_hot index bound byte,terminal_exact byte,terminal,tagMask,modes,known,inner]
  change Word64.concrete.select 255 ((state.value ||| VarintDecode.Spqr.payload byte index) &&& 4294967295) state.status = _
  exact Word64.select_accept _ _

theorem core_type_terminal (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (index : Nat) (bound : index < 10) (byte : BitVec 8)
    (modes : state.modes = [0,255,0,0]) (positions : state.positions = oneHot index)
    (known : state.scalarKnown = 255) (inner : state.inner = 0) (tag : state.tag = 1)
    (terminal : VarintDecode.Spqr.terminates byte = true) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.typeValue =
      (state.value ||| VarintDecode.Spqr.payload byte index) &&& 4294967295 := by
  change Word64.concrete.select
    (ByteAuth.concrete.and
      (ByteAuth.concrete.and
        (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 1)
          (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7))) state.scalarKnown)
      (ByteAuth.concrete.and (ByteAuth.concrete.not state.inner) (TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.tag 1)))
    (Word64.concrete.band
      (VarintDecode.Spqr.concrete.orWord state.value
        (TlsChatResponse.contribution VarintDecode.Spqr.concrete ByteAuth.concrete state.positions byte))
      (Word64.concrete.const 4294967295)) state.typeValue = _
  have tagMask : TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.tag 1 = 255 := by
    rw [tag]
    change Word64.eq Word64.concrete ByteAuth.concrete (1 : BitVec 64) 1 = 255
    unfold Word64.eq
    rw [ByteAuth.equalMask_value]
    simp
  rw [positions,contribution_one_hot index bound byte,terminal_exact byte,terminal,tagMask,modes,known,inner]
  change Word64.concrete.select 255 ((state.value ||| VarintDecode.Spqr.payload byte index) &&& 4294967295) state.typeValue = _
  exact Word64.select_accept _ _

#print axioms contribution_one_hot
#print axioms terminal_exact
#print axioms final_overflow_exact
#print axioms core_id_terminal
#print axioms core_status_terminal
#print axioms core_type_terminal
end ChatResponseReference.StreamingV1
