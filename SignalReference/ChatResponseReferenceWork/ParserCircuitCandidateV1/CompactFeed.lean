import ChatResponseReferenceWork.ParserCircuitCandidateV1.CompactCarry
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.ParserCircuitCandidateV1
set_option maxRecDepth 100000

def encodeCompactState (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64)) : List (BitVec 8) :=
  (compactEvent ⟨state,0,0,0⟩).take 582

theorem encode_state_controls (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (shape : MuxCodecShape state) (active beginning ending byte : BitVec 8) :
    encodeCompactInput state active beginning ending byte = encodeCompactState state ++ [active,beginning,ending,byte] :=
  encode_after_event ⟨state,0,0,0⟩ shape _ _ _ _

theorem event_state_carry (event : TlsChatResponseMux.Event (BitVec 8) (BitVec 64))
    (shape : MuxCodecShape event.state) : (compactEvent event).take 582 = encodeCompactState event.state := by
  have left := encode_after_event event shape 0 0 0 0
  have right := encode_state_controls event.state shape 0 0 0 0
  exact List.append_cancel_right (left.symm.trans right)

abbrev PrivateByteInput := BitVec 8 × BitVec 8 × BitVec 8 × BitVec 8

def compactFeedTrace (capacity : Nat) (encodedState : List (BitVec 8)) :
    List PrivateByteInput → List (List (BitVec 8))
  | [] => []
  | input::rest =>
    let output := runByte VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete capacity
      (encodedState ++ [input.1,input.2.1,input.2.2.1,input.2.2.2])
    output :: compactFeedTrace capacity (output.take 582) rest

def actualMuxByteTrace (capacity : Nat) (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64)) :
    List PrivateByteInput → List (List (BitVec 8))
  | [] => []
  | input::rest =>
    let event := TlsChatResponseMux.process VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      capacity state input.1 input.2.1 input.2.2.1 input.2.2.2
    compactEvent event :: actualMuxByteTrace capacity event.state rest

/-- Every encoded output byte agrees throughout the actual compact feedback
recurrence, including rejected intermediate states, private controls and resets. -/
theorem compact_feed_trace_eq (capacity : Nat) (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (inputs : List PrivateByteInput) (shape : MuxCodecShape state) (reachable : ReachableStack state.parser) :
    compactFeedTrace capacity (encodeCompactState state) inputs = actualMuxByteTrace capacity state inputs := by
  induction inputs generalizing state with
  | nil => rfl
  | cons input rest ih =>
    simp only [compactFeedTrace,actualMuxByteTrace]
    rw [←encode_state_controls state shape,encoded_byte_step capacity state shape reachable.2]
    congr 1
    have nextShape := mux_process_codec_shape capacity state input.1 input.2.1 input.2.2.1 input.2.2.2 shape
    rw [event_state_carry _ nextShape]
    exact ih _ nextShape (mux_process_reachable capacity state _ _ _ _ reachable)

/-- Initial admission/control prefixes may be arbitrary actual Mux operations.
This theorem concerns the subsequent byte circuit recurrence. It does not claim
an exported compact admission circuit has been provided or measured. -/
theorem admitted_compact_feed_trace_eq (capacity : Nat) (prefixInputs : List MuxInput) (inputs : List PrivateByteInput) :
    let state := muxRun capacity (TlsChatResponseMux.initial Word64.concrete ByteAuth.concrete capacity) prefixInputs
    compactFeedTrace capacity (encodeCompactState state) inputs = actualMuxByteTrace capacity state inputs := by
  apply compact_feed_trace_eq
  · exact mux_run_codec_shape capacity _ prefixInputs (mux_codec_initial_shape capacity)
  · exact fresh_muxRun_reachable capacity prefixInputs

#print axioms event_state_carry
#print axioms compact_feed_trace_eq
#print axioms admitted_compact_feed_trace_eq
end ChatResponseReference.ParserCircuitCandidateV1
