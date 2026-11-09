import ChatResponseReferenceWork.ParserCircuitCandidateV1.CompiledEncodedByte
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.ParserCircuitCandidateV1
set_option maxRecDepth 100000

theorem retained_state_bound : ∀ index : Fin 582, retainedIndex index.val < 982 := by
  decide +kernel

theorem compact_event_length (event : TlsChatResponseMux.Event (BitVec 8) (BitVec 64)) :
    (compactEvent event).length = 585 := by
  simp only [compactEvent,compactOutput,List.length_map,List.length_range,compactOutputSize]

theorem compact_input_length (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (active beginning ending byte : BitVec 8) :
    (encodeCompactInput state active beginning ending byte).length = 586 := by
  simp only [encodeCompactInput,compactInput,List.length_map,List.length_range]

theorem encode_after_event (event : TlsChatResponseMux.Event (BitVec 8) (BitVec 64))
    (shape : MuxCodecShape event.state) (active beginning ending byte : BitVec 8) :
    encodeCompactInput event.state active beginning ending byte =
    (compactEvent event).take 582 ++ [active,beginning,ending,byte] := by
  have takeLength : ((compactEvent event).take 582).length = 582 := by
    simp only [List.length_take,compact_event_length]
    rfl
  have rightLength : ((compactEvent event).take 582 ++ [active,beginning,ending,byte]).length = 586 := by
    simp only [List.length_append,takeLength,List.length_cons,List.length_nil]
  apply List.ext_getElem ((compact_input_length _ _ _ _ _).trans rightLength.symm)
  intro index left right
  have bound : index < 586 := by simpa only [compact_input_length] using left
  have eq : TlsWebSocketUpgrade.get ByteAuth.concrete
      (encodeCompactInput event.state active beginning ending byte) index =
      TlsWebSocketUpgrade.get ByteAuth.concrete ((compactEvent event).take 582 ++ [active,beginning,ending,byte]) index := by
    change TlsWebSocketUpgrade.get ByteAuth.concrete (compactInput ByteAuth.concrete _) index = _
    rw [get_compact_input ByteAuth.concrete _ index bound,get_appended ByteAuth.concrete _ _ index]
    simp only [takeLength]
    by_cases first : index < 582
    · simp only [first,if_pos]
      have retained := retained_state_bound ⟨index,first⟩
      have takeEq := get_slice ByteAuth.concrete (compactEvent event) 0 582 index first
      simp only [List.drop_zero,Nat.zero_add] at takeEq
      rw [takeEq]
      change _ = TlsWebSocketUpgrade.get ByteAuth.concrete (compactOutput ByteAuth.concrete _) index
      rw [get_compact ByteAuth.concrete _ index (by omega)]
      simp only [get_appended,mux_bytes_length event.state shape,retained,if_pos]
    · have not73 : ¬index < 73 := by omega
      have not473 : ¬index < 473 := by omega
      have not982 : ¬index+400 < 982 := by omega
      have offset : index+400-982 = index-582 := by omega
      simp only [first,if_false,retainedIndex,not73,not473,get_appended,mux_bytes_length event.state shape,not982,offset]
  simpa only [TlsWebSocketUpgrade.get,List.getElem?_eq_getElem left,List.getElem?_eq_getElem right,Option.getD_some] using eq

#print axioms retained_state_bound
#print axioms encode_after_event
end ChatResponseReference.ParserCircuitCandidateV1
