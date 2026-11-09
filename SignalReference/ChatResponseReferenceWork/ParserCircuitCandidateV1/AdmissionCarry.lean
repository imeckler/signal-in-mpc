import ChatResponseReferenceWork.ParserCircuitCandidateV1.CompiledAdmission
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.ParserCircuitCandidateV1
set_option maxRecDepth 100000

theorem compact_state_length (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64)) :
    (encodeCompactState state).length = 582 := by
  simp only [encodeCompactState,List.length_take,compact_event_length]
  rfl

theorem get_encoded_state (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (shape : MuxCodecShape state) (index : Nat) (bound : index < 582) :
    TlsWebSocketUpgrade.get ByteAuth.concrete (encodeCompactState state) index =
    TlsWebSocketUpgrade.get ByteAuth.concrete (TlsChatResponseMux.stateBytes Word64.concrete state) (retainedIndex index) := by
  have takeEq := get_slice ByteAuth.concrete (compactEvent ⟨state,0,0,0⟩) 0 582 index bound
  simp only [List.drop_zero,Nat.zero_add] at takeEq
  unfold encodeCompactState
  rw [takeEq]
  change TlsWebSocketUpgrade.get ByteAuth.concrete (compactOutput ByteAuth.concrete _) index = _
  rw [get_compact ByteAuth.concrete _ index (by omega)]
  simp only [get_appended,mux_bytes_length state shape,(retained_state_bound ⟨index,bound⟩),if_pos]

theorem encode_admit_payload_feedback (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (shape : MuxCodecShape state) (payload : List (BitVec 8)) (payloadLength : payload.length = 10) :
    compactAdmitInput ByteAuth.concrete (TlsChatResponseMux.stateBytes Word64.concrete state ++ payload) =
    encodeCompactState state ++ payload := by
  have leftLength : (compactAdmitInput ByteAuth.concrete
      (TlsChatResponseMux.stateBytes Word64.concrete state ++ payload)).length = 592 := by
    simp only [compactAdmitInput,List.length_map,List.length_range]
  have rightLength : (encodeCompactState state ++ payload).length = 592 := by
    rw [List.length_append,compact_state_length,payloadLength]
  apply List.ext_getElem (leftLength.trans rightLength.symm)
  intro index left right
  have bound : index < 592 := by simpa only [leftLength] using left
  have eq : TlsWebSocketUpgrade.get ByteAuth.concrete
      (compactAdmitInput ByteAuth.concrete (TlsChatResponseMux.stateBytes Word64.concrete state ++ payload)) index =
      TlsWebSocketUpgrade.get ByteAuth.concrete (encodeCompactState state ++ payload) index := by
    rw [get_compact_admit_input ByteAuth.concrete _ index bound,get_appended ByteAuth.concrete _ _ index]
    simp only [compact_state_length]
    by_cases first : index < 582
    · simp only [first,if_pos]
      rw [get_encoded_state state shape index first]
      simp only [get_appended,mux_bytes_length state shape,(retained_state_bound ⟨index,first⟩),if_pos]
    · have not73 : ¬index < 73 := by omega
      have not473 : ¬index < 473 := by omega
      have not982 : ¬index+400 < 982 := by omega
      have offset : index+400-982 = index-582 := by omega
      simp only [first,if_false,retainedIndex,not73,not473,get_appended,mux_bytes_length state shape,not982,offset]
  simpa only [TlsWebSocketUpgrade.get,List.getElem?_eq_getElem left,List.getElem?_eq_getElem right,Option.getD_some] using eq

theorem encode_admit_feedback (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (shape : MuxCodecShape state) (index : BitVec 8) (id : BitVec 64) (valid : BitVec 8) :
    encodeCompactAdmit state index id valid =
    encodeCompactState state ++ [index] ++ Word64.bytes Word64.concrete id ++ [valid] := by
  have payloadLength : ([index] ++ Word64.bytes Word64.concrete id ++ [valid]).length = 10 := by
    simp only [List.length_append,Word64.bytes_length,List.length_cons,List.length_nil]
  simpa only [encodeCompactAdmit,List.append_assoc] using encode_admit_payload_feedback state shape _ payloadLength

#print axioms get_encoded_state
#print axioms encode_admit_feedback
end ChatResponseReference.ParserCircuitCandidateV1
