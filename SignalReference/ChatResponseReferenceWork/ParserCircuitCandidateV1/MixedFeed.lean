import ChatResponseReferenceWork.ParserCircuitCandidateV1.AdmissionCarry
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.ParserCircuitCandidateV1
set_option maxRecDepth 100000

def mixedCircuitStep (capacity : Nat) (encodedState : List (BitVec 8)) : MuxInput → List (BitVec 8)
  | .byte active beginning ending value =>
    runByte VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete capacity
      (encodedState ++ [active,beginning,ending,value])
  | .admit index id valid =>
    runAdmit Word64.concrete ByteAuth.concrete
      (encodedState ++ [index] ++ Word64.bytes Word64.concrete id ++ [valid])

def mixedSourceStep (capacity : Nat) (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64)) : MuxInput → List (BitVec 8)
  | .byte active beginning ending value =>
    compactEvent (TlsChatResponseMux.process VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      capacity state active beginning ending value)
  | .admit index id valid =>
    encodeCompactState (TlsChatResponseMux.admit Word64.concrete ByteAuth.concrete state index id valid)

theorem mixed_step_encoded (capacity : Nat) (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (input : MuxInput) (shape : MuxCodecShape state) (safe : SafeStack state.parser) :
    mixedCircuitStep capacity (encodeCompactState state) input = mixedSourceStep capacity state input := by
  cases input with
  | byte active beginning ending value =>
    change runByte _ _ _ _ _ = _
    rw [←encode_state_controls state shape,encoded_byte_step capacity state shape safe]
    rfl
  | admit index id valid =>
    change runAdmit _ _ _ = _
    rw [←encode_admit_feedback state shape,encoded_admit_step state shape]
    rfl

theorem mixed_source_carry (capacity : Nat) (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (input : MuxInput) (shape : MuxCodecShape state) :
    (mixedSourceStep capacity state input).take 582 = encodeCompactState (muxAdvance capacity state input) := by
  cases input with
  | byte active beginning ending value =>
    exact event_state_carry _ (mux_process_codec_shape capacity state _ _ _ _ shape)
  | admit index id valid =>
    change (encodeCompactState _).take 582 = _
    simpa only [compact_state_length,muxAdvance] using (List.take_length (l := encodeCompactState
      (TlsChatResponseMux.admit Word64.concrete ByteAuth.concrete state index id valid)))

def mixedCircuitTrace (capacity : Nat) (encodedState : List (BitVec 8)) : List MuxInput → List (List (BitVec 8))
  | [] => []
  | input::rest =>
    let output := mixedCircuitStep capacity encodedState input
    output :: mixedCircuitTrace capacity (output.take 582) rest

def mixedSourceTrace (capacity : Nat) (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64)) : List MuxInput → List (List (BitVec 8))
  | [] => []
  | input::rest =>
    mixedSourceStep capacity state input :: mixedSourceTrace capacity (muxAdvance capacity state input) rest

/-- Mixed byte and admission feedback is exact for every private payload and
control sequence, including failed admission and sticky rejection/reset paths. -/
theorem mixed_trace_eq (capacity : Nat) (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (inputs : List MuxInput) (shape : MuxCodecShape state) (reachable : ReachableStack state.parser) :
    mixedCircuitTrace capacity (encodeCompactState state) inputs = mixedSourceTrace capacity state inputs := by
  induction inputs generalizing state with
  | nil => rfl
  | cons input rest ih =>
    simp only [mixedCircuitTrace,mixedSourceTrace]
    rw [mixed_step_encoded capacity state input shape reachable.2,mixed_source_carry capacity state input shape]
    congr 1
    apply ih
    · cases input with
      | byte active beginning ending value => exact mux_process_codec_shape _ _ _ _ _ _ shape
      | admit index id valid => exact mux_admit_codec_shape _ _ _ _ shape
    · cases input with
      | byte active beginning ending value => exact mux_process_reachable _ _ _ _ _ _ reachable
      | admit index id valid => exact mux_admit_reachable _ _ _ _ reachable

theorem fresh_mixed_trace_eq (capacity : Nat) (inputs : List MuxInput) :
    mixedCircuitTrace capacity (encodeCompactState
      (TlsChatResponseMux.initial Word64.concrete ByteAuth.concrete capacity)) inputs =
    mixedSourceTrace capacity (TlsChatResponseMux.initial Word64.concrete ByteAuth.concrete capacity) inputs :=
  mixed_trace_eq capacity _ inputs (mux_codec_initial_shape capacity)
    ⟨initial_control_masks capacity 0,.inr (initial_narrow_stack capacity 0)⟩

#print axioms mixed_step_encoded
#print axioms mixed_source_carry
#print axioms mixed_trace_eq
#print axioms fresh_mixed_trace_eq
end ChatResponseReference.ParserCircuitCandidateV1
