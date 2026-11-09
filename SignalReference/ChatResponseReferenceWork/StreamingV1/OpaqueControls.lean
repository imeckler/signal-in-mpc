import ChatResponseReferenceWork.StreamingV1.ActualKnownKeyEntry
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1

theorem opaque_value_step (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 3) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.value = state.value := by
  have inactive : TlsWebSocketUpgrade.any ByteAuth.concrete ((lane 3).take 3) = 0 := rfl
  have zeroAnd (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  change Word64.concrete.select (ByteAuth.concrete.and (TlsWebSocketUpgrade.any ByteAuth.concrete (state.modes.take 3)) _) _
    (Word64.concrete.select (TlsWebSocketUpgrade.any ByteAuth.concrete (state.modes.take 3)) _ state.value) = _
  rw [modes,inactive,zeroAnd,Word64.select_reject,Word64.select_reject]

theorem opaque_positions_step (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 3) (shape : state.positions.length = 10) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.positions = state.positions := by
  have inactive : TlsWebSocketUpgrade.any ByteAuth.concrete ((lane 3).take 3) = 0 := rfl
  have zeroAnd (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  change TlsWebSocketUpgrade.choose ByteAuth.concrete
    (ByteAuth.concrete.and (TlsWebSocketUpgrade.any ByteAuth.concrete (state.modes.take 3)) _) _
    (TlsWebSocketUpgrade.choose ByteAuth.concrete (TlsWebSocketUpgrade.any ByteAuth.concrete (state.modes.take 3)) _ state.positions) = _
  rw [modes,inactive,zeroAnd]
  have reject : TlsWebSocketUpgrade.choose ByteAuth.concrete 0 (ByteAuth.concrete.const 0::state.positions.take 9) state.positions = state.positions :=
    choose_reject_exact _ _ (by simp only [List.length_cons,List.length_take,shape]; rfl)
  rw [reject]
  exact choose_reject_exact _ _ (by simpa only [TlsWebSocketUpgrade.initial,List.length_cons,List.length_replicate] using shape.symm)

theorem opaque_prefix_controls (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (bytes : List (BitVec 8)) (count : Nat) (bounded : count < 2^64)
    (fits : bytes.length ≤ count) (modes : state.modes = lane 3)
    (skip : state.skip = BitVec.ofNat 64 count) (shape : state.positions.length = 10) :
    (feed state bytes).positions = state.positions ∧ (feed state bytes).value = state.value := by
  induction bytes generalizing state count with
  | nil => exact ⟨rfl,rfl⟩
  | cons byte rest ih =>
    have firstPositions := opaque_positions_step state byte modes shape
    have firstValue := opaque_value_step state byte modes
    cases rest with
    | nil => exact ⟨firstPositions,firstValue⟩
    | cons following tail =>
      let next := (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state
      have first := opaque_prefix_inside state [byte] count bounded (by simp only [List.length_cons,List.length_nil] at fits ⊢; omega) modes skip
      have result := ih next (count-1) (by omega) (by simp only [List.length_cons] at fits ⊢; omega) first.1 first.2
        (by rw [firstPositions]; exact shape)
      exact ⟨result.1.trans firstPositions,result.2.trans firstValue⟩

#print axioms opaque_value_step
#print axioms opaque_positions_step
#print axioms opaque_prefix_controls
end ChatResponseReference.StreamingV1
