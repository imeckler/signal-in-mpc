import ChatResponseReferenceWork.StreamingV1.NativeKeySpan
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1

/-- Exact list lengths required by the actual Core zipWith selectors. -/
structure StateShape (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) : Prop where
  modes : state.modes.length = 4
  positions : state.positions.length = 10
  kinds : state.kinds.length = 4
  stack : state.stack.length = 100
  utf : state.utf.length = 8

theorem initial_shape (capacity : Nat) (expected : BitVec 64) :
    StateShape (TlsChatResponse.initial Word64.concrete ByteAuth.concrete capacity expected) := by
  constructor <;> rfl

theorem step_shape (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (shape : StateShape state) :
    StateShape (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state := by
  constructor
  · change [_,_,_,_].length = 4; rfl
  · change (TlsWebSocketUpgrade.choose ByteAuth.concrete _ (TlsWebSocketUpgrade.initial ByteAuth.concrete 9)
      (TlsWebSocketUpgrade.choose ByteAuth.concrete _ (0::state.positions.take 9) state.positions)).length = 10
    simp only [TlsWebSocketUpgrade.choose,TlsWebSocketUpgrade.initial,List.length_zipWith,
      List.length_cons,List.length_replicate,List.length_take,shape.positions]
    rfl
  · exact key_kinds_shape state byte shape.kinds
  · change (state.stack.zipIdx.map _).length = 100
    rw [List.length_map,List.length_zipIdx,shape.stack]
  · change (TlsWebSocketUpgrade.choose ByteAuth.concrete _ (TlsWebSocketUpgrade.initial ByteAuth.concrete 7)
      (TlsWebSocketUpgrade.choose ByteAuth.concrete _ (TlsWebSocketFrame.utfStep ByteAuth.concrete state.utf byte) state.utf)).length = 8
    have utfLength : (TlsWebSocketFrame.utfStep ByteAuth.concrete state.utf byte).length = 8 := rfl
    simp only [TlsWebSocketUpgrade.choose,TlsWebSocketUpgrade.initial,List.length_zipWith,
      List.length_cons,List.length_replicate,utfLength,shape.utf]
    rfl

theorem finish_shape (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (shape : StateShape state) :
    StateShape (TlsChatResponse.finish Word64.concrete ByteAuth.concrete state) := by
  exact ⟨shape.modes,shape.positions,shape.kinds,shape.stack,shape.utf⟩

theorem feed_shape (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (bytes : List (BitVec 8))
    (shape : StateShape state) : StateShape (feed state bytes) := by
  induction bytes generalizing state with
  | nil => exact shape
  | cons byte rest ih => exact ih _ (step_shape state byte shape)

theorem select_shape (mask : BitVec 8) (yes no : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (yesShape : StateShape yes) (noShape : StateShape no) :
    StateShape (TlsChatResponse.stateSelect Word64.concrete ByteAuth.concrete mask yes no) := by
  constructor <;> simp only [TlsChatResponse.stateSelect,TlsWebSocketUpgrade.choose,List.length_zipWith,
    yesShape.modes,noShape.modes,yesShape.positions,noShape.positions,yesShape.kinds,noShape.kinds,
    yesShape.stack,noShape.stack,yesShape.utf,noShape.utf] <;> rfl

/-- Even malformed control flags retain the fixed state layout. -/
theorem process_shape (capacity : Nat) (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (active beginning ending byte : BitVec 8) (shape : StateShape state) :
    StateShape (TlsChatResponse.process VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      capacity state active beginning ending byte).state := by
  let fresh := {TlsChatResponse.initial Word64.concrete ByteAuth.concrete capacity state.expected with
    valid := ByteAuth.concrete.and state.valid (ByteAuth.concrete.not state.seen),seen := ByteAuth.concrete.const 255}
  let started := TlsChatResponse.stateSelect Word64.concrete ByteAuth.concrete
    (TlsWebSocketUpgrade.eq ByteAuth.concrete beginning 255) fresh state
  let event := TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete started byte
  let selected := TlsChatResponse.stateSelect Word64.concrete ByteAuth.concrete
    (TlsWebSocketUpgrade.eq ByteAuth.concrete active 255) event.state started
  let canonical := (active::beginning::ending::[]).foldl (fun valid mask => ByteAuth.concrete.and valid
    (TlsWebSocketUpgrade.either ByteAuth.concrete (TlsWebSocketUpgrade.eq ByteAuth.concrete mask 0)
      (TlsWebSocketUpgrade.eq ByteAuth.concrete mask 255))) (ByteAuth.concrete.const 255)
  let guarded := {selected with valid := ByteAuth.concrete.and selected.valid canonical}
  have base := initial_shape capacity state.expected
  have freshShape : StateShape fresh := ⟨base.modes,base.positions,base.kinds,base.stack,base.utf⟩
  have startedShape : StateShape started := select_shape _ fresh state freshShape shape
  have selectedShape : StateShape selected := select_shape _ event.state started (step_shape started byte startedShape) startedShape
  have guardedShape : StateShape guarded :=
    ⟨selectedShape.modes,selectedShape.positions,selectedShape.kinds,selectedShape.stack,selectedShape.utf⟩
  change StateShape (TlsChatResponse.stateSelect Word64.concrete ByteAuth.concrete
    (TlsWebSocketUpgrade.eq ByteAuth.concrete ending 255)
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete guarded) guarded)
  exact select_shape _ _ guarded (finish_shape guarded guardedShape) guardedShape

#print axioms initial_shape
#print axioms step_shape
#print axioms finish_shape
#print axioms feed_shape
#print axioms select_shape
#print axioms process_shape
end ChatResponseReference.StreamingV1
