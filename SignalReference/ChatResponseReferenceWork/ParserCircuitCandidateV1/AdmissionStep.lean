import ChatResponseReferenceWork.ParserCircuitCandidateV1.AdmissionCodec
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.ParserCircuitCandidateV1
set_option maxRecDepth 100000

theorem mux_runAdmit_encoded (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (shape : MuxCodecShape state) (index : BitVec 8) (id : BitVec 64) (valid : BitVec 8) :
    TlsChatResponseMux.runAdmit Word64.concrete ByteAuth.concrete
      (TlsChatResponseMux.stateBytes Word64.concrete state ++ [index] ++ Word64.bytes Word64.concrete id ++ [valid]) =
    TlsChatResponseMux.stateBytes Word64.concrete (TlsChatResponseMux.admit Word64.concrete ByteAuth.concrete state index id valid) := by
  have length := mux_bytes_length state shape
  have takeState : (TlsChatResponseMux.stateBytes Word64.concrete state).take 982 =
      TlsChatResponseMux.stateBytes Word64.concrete state := by
    simpa only [length] using (List.take_length (l := TlsChatResponseMux.stateBytes Word64.concrete state))
  have dropState n (bound : 982 ≤ n) : (TlsChatResponseMux.stateBytes Word64.concrete state).drop n = [] :=
    List.drop_eq_nil_of_le (by rw [length]; exact bound)
  have takeWord : (Word64.bytes Word64.concrete id).take 8 = Word64.bytes Word64.concrete id := by
    simpa only [Word64.bytes_length] using (List.take_length (l := Word64.bytes Word64.concrete id))
  have dropWord : (Word64.bytes Word64.concrete id).drop 8 = [] := List.drop_eq_nil_of_le (by rw [Word64.bytes_length]; omega)
  simp [TlsChatResponseMux.runAdmit,TlsChatResponseMux.stateSize,List.drop_append,List.append_assoc,
    get_appended,length,takeState,dropState,takeWord,dropWord,Word64.bytes_length,pack_word_bytes,read_encoded_mux state shape]
  simp [TlsWebSocketUpgrade.get,List.getElem?_append,Word64.bytes_length]

theorem admit_trim_commutes (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (index : BitVec 8) (id : BitVec 64) (valid : BitVec 8) :
    TlsChatResponseMux.admit Word64.concrete ByteAuth.concrete (trimMuxState state) index id valid =
    trimMuxState (TlsChatResponseMux.admit Word64.concrete ByteAuth.concrete state index id valid) := rfl

theorem encoded_admit_step (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (shape : MuxCodecShape state) (index : BitVec 8) (id : BitVec 64) (valid : BitVec 8) :
    runAdmit Word64.concrete ByteAuth.concrete (encodeCompactAdmit state index id valid) =
    encodeCompactState (TlsChatResponseMux.admit Word64.concrete ByteAuth.concrete state index id valid) := by
  unfold runAdmit
  rw [expand_encoded_admit state shape,mux_runAdmit_encoded _ (mux_trim_codec_shape state shape)]
  have nextShape := mux_admit_codec_shape state index id valid shape
  have projectedShape := mux_admit_codec_shape (trimMuxState state) index id valid (mux_trim_codec_shape state shape)
  rw [←List.append_nil (TlsChatResponseMux.stateBytes Word64.concrete
    (TlsChatResponseMux.admit Word64.concrete ByteAuth.concrete (trimMuxState state) index id valid))]
  rw [compact_state_suffix _ projectedShape,admit_trim_commutes,encode_compact_state_trim _ nextShape]

#print axioms mux_runAdmit_encoded
#print axioms admit_trim_commutes
#print axioms encoded_admit_step
end ChatResponseReference.ParserCircuitCandidateV1
