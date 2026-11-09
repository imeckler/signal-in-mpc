import ChatResponseReferenceWork.ParserCircuitCandidateV1.CompactFeed
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.ParserCircuitCandidateV1
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def compactAdmitInput (a : ByteAuth.Ops B) (full : List B) : List B :=
  (List.range 592).map (fun i => TlsWebSocketUpgrade.get a full (retainedIndex i))

def expandAdmitInput (a : ByteAuth.Ops B) (compact : List B) : List B :=
  (List.range 992).map (fun i => match expandedSourceIndex i with
    | none => a.const 0
    | some source => TlsWebSocketUpgrade.get a compact source)

def compactAdmitOutput (a : ByteAuth.Ops B) (full : List B) : List B :=
  (compactOutput a full).take 582

@[irreducible] def runAdmit (o : Word64.Ops B W) (a : ByteAuth.Ops B) (raw : List B) : List B :=
  compactAdmitOutput a (TlsChatResponseMux.runAdmit o a (expandAdmitInput a raw))

def encodeCompactAdmit (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (index : BitVec 8) (id : BitVec 64) (valid : BitVec 8) : List (BitVec 8) :=
  compactAdmitInput ByteAuth.concrete (TlsChatResponseMux.stateBytes Word64.concrete state ++
    [index] ++ Word64.bytes Word64.concrete id ++ [valid])

def expandedAdmitTest (index : Nat) : Bool :=
  match expandedSourceIndex index with
  | none => true
  | some compact => decide (compact < 592 ∧ retainedIndex compact = index)

theorem expanded_admit_test : ∀ index : Fin 992, expandedAdmitTest index.val = true := by
  decide +kernel

theorem get_compact_admit_input (a : ByteAuth.Ops B) (raw : List B) (index : Nat) (bound : index < 592) :
    TlsWebSocketUpgrade.get a (compactAdmitInput a raw) index =
    TlsWebSocketUpgrade.get a raw (retainedIndex index) := by
  simp [compactAdmitInput,TlsWebSocketUpgrade.get,bound]

theorem get_expanded_admit (a : ByteAuth.Ops B) (raw : List B) (index : Nat) (bound : index < 992) :
    TlsWebSocketUpgrade.get a (expandAdmitInput a raw) index =
    match expandedSourceIndex index with
    | none => a.const 0
    | some source => TlsWebSocketUpgrade.get a raw source := by
  simp [expandAdmitInput,TlsWebSocketUpgrade.get,bound]

theorem expand_compact_admit_get (a : ByteAuth.Ops B) (raw : List B) (index : Nat) (bound : index < 992) :
    TlsWebSocketUpgrade.get a (expandAdmitInput a (compactAdmitInput a raw)) index = projectedByte a raw index := by
  rw [get_expanded_admit a _ index bound]
  have inverse := expanded_admit_test ⟨index,bound⟩
  unfold projectedByte expandedAdmitTest at *
  cases source : expandedSourceIndex index with
  | none => rfl
  | some compact =>
    simp only [source] at inverse ⊢
    have correct : compact < 592 ∧ retainedIndex compact = index := of_decide_eq_true inverse
    rw [get_compact_admit_input a raw compact correct.1,correct.2]

theorem expand_admit_length (a : ByteAuth.Ops B) (raw : List B) : (expandAdmitInput a raw).length = 992 := by
  simp only [expandAdmitInput,List.length_map,List.length_range]

theorem expand_admit_payload (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (shape : MuxCodecShape state) (payload : List (BitVec 8)) (payloadLength : payload.length = 10) :
    expandAdmitInput ByteAuth.concrete
      (compactAdmitInput ByteAuth.concrete (TlsChatResponseMux.stateBytes Word64.concrete state ++ payload)) =
    TlsChatResponseMux.stateBytes Word64.concrete (trimMuxState state) ++ payload := by
  have leftLength := expand_admit_length ByteAuth.concrete
    (compactAdmitInput ByteAuth.concrete (TlsChatResponseMux.stateBytes Word64.concrete state ++ payload))
  have rightLength : (TlsChatResponseMux.stateBytes Word64.concrete (trimMuxState state) ++ payload).length = 992 := by
    rw [List.length_append,mux_bytes_length _ (mux_trim_codec_shape state shape),payloadLength]
  apply List.ext_getElem (leftLength.trans rightLength.symm)
  intro i left right
  have bound : i < 992 := by simpa only [leftLength] using left
  have eq := (expand_compact_admit_get ByteAuth.concrete
    (TlsChatResponseMux.stateBytes Word64.concrete state ++ payload) i bound).trans
    (serialized_mux_trim_get state shape payload i).symm
  simpa only [TlsWebSocketUpgrade.get,List.getElem?_eq_getElem left,List.getElem?_eq_getElem right,
    Option.getD_some] using eq

theorem expand_encoded_admit (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (shape : MuxCodecShape state) (index : BitVec 8) (id : BitVec 64) (valid : BitVec 8) :
    expandAdmitInput ByteAuth.concrete (encodeCompactAdmit state index id valid) =
    TlsChatResponseMux.stateBytes Word64.concrete (trimMuxState state) ++
      [index] ++ Word64.bytes Word64.concrete id ++ [valid] := by
  have payloadLength : ([index] ++ Word64.bytes Word64.concrete id ++ [valid]).length = 10 := by
    simp only [List.length_append,Word64.bytes_length,List.length_cons,List.length_nil]
  simpa only [encodeCompactAdmit,List.append_assoc] using expand_admit_payload state shape _ payloadLength

theorem compact_state_suffix (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (shape : MuxCodecShape state) (suffix : List (BitVec 8)) :
    compactAdmitOutput ByteAuth.concrete (TlsChatResponseMux.stateBytes Word64.concrete state ++ suffix) =
    encodeCompactState state := by
  unfold compactAdmitOutput encodeCompactState compactEvent compactOutput
  simp only [←List.map_take,List.take_range,compactOutputSize]
  apply List.map_congr_left
  intro index member
  have bound : index < 582 := List.mem_range.mp member
  have retained := retained_state_bound ⟨index,bound⟩
  simp only [get_appended,mux_bytes_length state shape,retained,if_pos]

theorem encode_compact_state_trim (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (shape : MuxCodecShape state) : encodeCompactState (trimMuxState state) = encodeCompactState state :=
  congrArg (List.take 582) (compact_trim_event ⟨state,0,0,0⟩ shape)

#print axioms expanded_admit_test
#print axioms expand_encoded_admit
#print axioms compact_state_suffix
end ChatResponseReference.ParserCircuitCandidateV1
