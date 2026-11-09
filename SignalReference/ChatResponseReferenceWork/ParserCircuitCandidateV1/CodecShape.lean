import ChatResponseReferenceWork.ParserCircuitCandidateV1.MuxCodec
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.ParserCircuitCandidateV1
-- Reuses the factored shape argument from StreamingV1.StateShape, without its
-- native-source extraction dependencies. No runtime body is modified.
theorem codec_initial_shape (capacity : Nat) (expected : BitVec 64) :
    CodecShape (TlsChatResponse.initial Word64.concrete ByteAuth.concrete capacity expected) := by
  constructor <;> rfl

theorem codec_step_shape (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (shape : CodecShape state) :
    CodecShape (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state := by
  constructor
  · change [_,_,_,_].length = 4; rfl
  · change (TlsWebSocketUpgrade.choose ByteAuth.concrete _ (TlsWebSocketUpgrade.initial ByteAuth.concrete 9)
      (TlsWebSocketUpgrade.choose ByteAuth.concrete _ (0::state.positions.take 9) state.positions)).length = 10
    simp only [TlsWebSocketUpgrade.choose,TlsWebSocketUpgrade.initial,List.length_zipWith,
      List.length_cons,List.length_replicate,List.length_take,shape.positions]
    rfl
  · change (TlsWebSocketUpgrade.choose ByteAuth.concrete _ [_,_,_,_] state.kinds).length = 4
    simp only [TlsWebSocketUpgrade.choose,List.length_zipWith,List.length_cons,List.length_nil,shape.kinds]
    rfl
  · change (state.stack.zipIdx.map _).length = 100
    rw [List.length_map,List.length_zipIdx,shape.stack]
  · change (TlsWebSocketUpgrade.choose ByteAuth.concrete _ (TlsWebSocketUpgrade.initial ByteAuth.concrete 7)
      (TlsWebSocketUpgrade.choose ByteAuth.concrete _ (TlsWebSocketFrame.utfStep ByteAuth.concrete state.utf byte) state.utf)).length = 8
    have utfLength : (TlsWebSocketFrame.utfStep ByteAuth.concrete state.utf byte).length = 8 := rfl
    simp only [TlsWebSocketUpgrade.choose,TlsWebSocketUpgrade.initial,List.length_zipWith,
      List.length_cons,List.length_replicate,utfLength,shape.utf]
    rfl

theorem codec_finish_shape (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (shape : CodecShape state) :
    CodecShape (TlsChatResponse.finish Word64.concrete ByteAuth.concrete state) := by
  exact ⟨shape.modes,shape.positions,shape.kinds,shape.stack,shape.utf⟩

theorem codec_select_shape (mask : BitVec 8) (yes no : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (yesShape : CodecShape yes) (noShape : CodecShape no) :
    CodecShape (TlsChatResponse.stateSelect Word64.concrete ByteAuth.concrete mask yes no) := by
  constructor <;> simp only [TlsChatResponse.stateSelect,TlsWebSocketUpgrade.choose,List.length_zipWith,
    yesShape.modes,noShape.modes,yesShape.positions,noShape.positions,yesShape.kinds,noShape.kinds,
    yesShape.stack,noShape.stack,yesShape.utf,noShape.utf] <;> rfl

/-- Even malformed control flags retain the fixed state layout. -/
theorem codec_process_shape (capacity : Nat) (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (active beginning ending byte : BitVec 8) (shape : CodecShape state) :
    CodecShape (TlsChatResponse.process VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
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
  have base := codec_initial_shape capacity state.expected
  have freshShape : CodecShape fresh := ⟨base.modes,base.positions,base.kinds,base.stack,base.utf⟩
  have startedShape : CodecShape started := codec_select_shape _ fresh state freshShape shape
  have selectedShape : CodecShape selected := codec_select_shape _ event.state started (codec_step_shape started byte startedShape) startedShape
  have guardedShape : CodecShape guarded :=
    ⟨selectedShape.modes,selectedShape.positions,selectedShape.kinds,selectedShape.stack,selectedShape.utf⟩
  change CodecShape (TlsChatResponse.stateSelect Word64.concrete ByteAuth.concrete
    (TlsWebSocketUpgrade.eq ByteAuth.concrete ending 255)
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete guarded) guarded)
  exact codec_select_shape _ _ guarded (codec_finish_shape guarded guardedShape) guardedShape

theorem codec_trim_shape (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (shape : CodecShape state) :
    CodecShape (trimStack state) := by
  constructor
  · exact shape.modes
  · exact shape.positions
  · exact shape.kinds
  · simpa only [trimStack,List.length_map] using shape.stack
  · exact shape.utf

#print axioms codec_initial_shape
#print axioms codec_step_shape
#print axioms codec_process_shape
#print axioms codec_trim_shape
end ChatResponseReference.ParserCircuitCandidateV1
