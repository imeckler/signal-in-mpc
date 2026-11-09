import ChatResponseReferenceWork.ParserCircuitCandidateV1.CodecShape
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.ParserCircuitCandidateV1
set_option maxRecDepth 100000

theorem mux_codec_initial_shape (capacity : Nat) :
    MuxCodecShape (TlsChatResponseMux.initial Word64.concrete ByteAuth.concrete capacity) :=
  ⟨codec_initial_shape capacity 0,rfl,rfl⟩

theorem correlated_codec_shape (capacity : Nat) (parsed : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (valid done : BitVec 8) (shape : CodecShape parsed) :
    CodecShape (TlsChatResponseMux.validCore
      (TlsChatResponse.stateSelect Word64.concrete ByteAuth.concrete done
        (TlsChatResponseMux.validCore (TlsChatResponse.initial Word64.concrete ByteAuth.concrete capacity 0) valid) parsed) valid) := by
  have base := codec_initial_shape capacity 0
  have reset : CodecShape (TlsChatResponseMux.validCore
      (TlsChatResponse.initial Word64.concrete ByteAuth.concrete capacity 0) valid) :=
    ⟨base.modes,base.positions,base.kinds,base.stack,base.utf⟩
  have selected := codec_select_shape done _ parsed reset shape
  exact ⟨selected.modes,selected.positions,selected.kinds,selected.stack,selected.utf⟩

theorem mux_tail_codec_shape (capacity : Nat) (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (beginning ending : BitVec 8) (parsed : TlsChatResponse.Event (BitVec 8) (BitVec 64))
    (shape : MuxCodecShape state) (parsedShape : CodecShape parsed.state) :
    MuxCodecShape (muxTail capacity state beginning ending parsed).state := by
  constructor
  · exact correlated_codec_shape capacity parsed.state _ _ parsedShape
  · change (List.zipWith _ (state.slots.map _) ((state.slots.map _).map _)).length = 4
    simp only [List.length_zipWith,List.length_map,shape.slots]
    rfl
  · change ((List.range 4).map _).length = 4
    simp

theorem mux_process_codec_shape (capacity : Nat) (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (active beginning ending byte : BitVec 8) (shape : MuxCodecShape state) :
    MuxCodecShape (TlsChatResponseMux.process VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      capacity state active beginning ending byte).state := by
  rw [mux_process_as_tail]
  exact mux_tail_codec_shape _ _ _ _ _ shape (codec_process_shape _ _ _ _ _ _ shape.parser)

theorem mux_admit_codec_shape (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (index : BitVec 8) (id : BitVec 64) (valid : BitVec 8) (shape : MuxCodecShape state) :
    MuxCodecShape (TlsChatResponseMux.admit Word64.concrete ByteAuth.concrete state index id valid) := by
  constructor
  · exact shape.parser
  · change (state.slots.zipIdx.map _).length = 4
    simpa only [List.length_map,List.length_zipIdx] using shape.slots
  · exact shape.rows

theorem mux_trim_codec_shape (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64)) (shape : MuxCodecShape state) :
    MuxCodecShape (trimMuxState state) := ⟨codec_trim_shape state.parser shape.parser,shape.slots,shape.rows⟩

theorem mux_run_codec_shape (capacity : Nat) (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (inputs : List MuxInput) (shape : MuxCodecShape state) : MuxCodecShape (muxRun capacity state inputs) := by
  induction inputs generalizing state with
  | nil => exact shape
  | cons input rest ih =>
    apply ih
    cases input with
    | byte active beginning ending value => exact mux_process_codec_shape _ _ _ _ _ _ shape
    | admit index id valid => exact mux_admit_codec_shape _ _ _ _ shape

#print axioms mux_codec_initial_shape
#print axioms mux_process_codec_shape
#print axioms mux_admit_codec_shape
#print axioms mux_trim_codec_shape
#print axioms mux_run_codec_shape
end ChatResponseReference.ParserCircuitCandidateV1
