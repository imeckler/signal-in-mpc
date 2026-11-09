import ChatResponseReferenceWork.StreamingV1.StateSelection
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
set_option maxHeartbeats 1000000

/-- Actual production process ignores an inactive byte completely, including
all parser state and body/header event masks. No assumption on padding data. -/
theorem process_inactive (capacity : Nat) (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (byte : BitVec 8) (shape : StateShape state) :
    TlsChatResponse.process VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      capacity state 0 0 0 byte = ⟨state,0,0,0⟩ := by
  let fresh := {TlsChatResponse.initial Word64.concrete ByteAuth.concrete capacity state.expected with
    valid := ByteAuth.concrete.and state.valid (ByteAuth.concrete.not state.seen),seen := ByteAuth.concrete.const 255}
  have baseShape := initial_shape capacity state.expected
  have freshShape : StateShape fresh := ⟨baseShape.modes,baseShape.positions,baseShape.kinds,baseShape.stack,baseShape.utf⟩
  have off : TlsWebSocketUpgrade.eq ByteAuth.concrete 0 255 = 0 := rfl
  have hot (x : BitVec 8) : ByteAuth.concrete.and x 255 = x := BitVec.and_allOnes
  have andZero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  have zeroAnd (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  unfold TlsChatResponse.process
  simp only [off]
  rw [state_select_reject fresh state freshShape shape]
  rw [state_select_reject _ state (step_shape state byte shape) shape]
  let selected := {state with valid := ByteAuth.concrete.and state.valid 255}
  change (⟨TlsChatResponse.stateSelect Word64.concrete ByteAuth.concrete 0
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete selected) selected,_,_,_⟩ : TlsChatResponse.Event (BitVec 8) (BitVec 64)) = _
  have selectedEq : selected = state := by
    dsimp only [selected]
    rw [hot]
  rw [selectedEq,state_select_reject _ state (finish_shape state shape) shape]
  simp only [andZero,zeroAnd]

/-- Any amount or contents of inactive capacity tail preserves the complete
actual process state. This is a process-level padding theorem, not EOF validity. -/
theorem inactive_padding_exact (capacity : Nat) (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (padding : List (BitVec 8)) (shape : StateShape state) :
    padding.foldl (fun current byte =>
      (TlsChatResponse.process VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
        capacity current 0 0 0 byte).state) state = state := by
  induction padding generalizing state with
  | nil => rfl
  | cons byte rest ih =>
    rw [List.foldl_cons,process_inactive capacity state byte shape]
    exact ih state shape

theorem runByte_inactive (capacity : Nat) (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (raw : List (BitVec 8)) (shape : StateShape state)
    (decoded : TlsChatResponse.readState Word64.concrete ByteAuth.concrete (raw.take TlsChatResponse.stateSize) = state)
    (active : TlsWebSocketUpgrade.get ByteAuth.concrete raw TlsChatResponse.stateSize = 0)
    (beginning : TlsWebSocketUpgrade.get ByteAuth.concrete raw (TlsChatResponse.stateSize+1) = 0)
    (ending : TlsWebSocketUpgrade.get ByteAuth.concrete raw (TlsChatResponse.stateSize+2) = 0) :
    TlsChatResponse.runByte VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete capacity raw =
      [state.valid,state.finished,state.successful,0,0,0] ++ TlsChatResponse.stateBytes Word64.concrete state := by
  unfold TlsChatResponse.runByte
  rw [decoded,active,beginning,ending,process_inactive capacity state _ shape]

#print axioms process_inactive
#print axioms inactive_padding_exact
#print axioms runByte_inactive
end ChatResponseReference.StreamingV1
