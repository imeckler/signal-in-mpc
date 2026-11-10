import ChatResponseReferenceWork.ParserCircuitCandidateV1.StateCodec
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.ParserCircuitCandidateV1
-- Unaccepted incomplete roundtrip draft; not part of the checked module graph.
set_option maxHeartbeats 2000000
theorem read_encoded_state (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (shape : CodecShape state) :
    TlsChatResponse.readState Word64.concrete ByteAuth.concrete
      (TlsChatResponse.stateBytes Word64.concrete state) = state := by
  have dropModes n (bound : 4 ≤ n) : state.modes.drop n = [] := List.drop_eq_nil_of_le (by rw [shape.modes]; exact bound)
  have dropPositions n (bound : 10 ≤ n) : state.positions.drop n = [] := List.drop_eq_nil_of_le (by rw [shape.positions]; exact bound)
  have dropKinds n (bound : 4 ≤ n) : state.kinds.drop n = [] := List.drop_eq_nil_of_le (by rw [shape.kinds]; exact bound)
  have dropUtf n (bound : 8 ≤ n) : state.utf.drop n = [] := List.drop_eq_nil_of_le (by rw [shape.utf]; exact bound)
  have dropWord word n (bound : 8 ≤ n) : (Word64.bytes Word64.concrete word).drop n = [] :=
    List.drop_eq_nil_of_le (by rw [Word64.bytes_length]; exact bound)
  have dropStack n (bound : 800 ≤ n) : (state.stack.flatMap (Word64.bytes Word64.concrete)).drop n = [] :=
    List.drop_eq_nil_of_le (by rw [word_chunks_length,shape.stack]; exact bound)
  have takeModes : state.modes.take 4 = state.modes := by simpa only [shape.modes] using (List.take_length (l := state.modes))
  have takePositions : state.positions.take 10 = state.positions := by simpa only [shape.positions] using (List.take_length (l := state.positions))
  have takeKinds : state.kinds.take 4 = state.kinds := by simpa only [shape.kinds] using (List.take_length (l := state.kinds))
  have takeUtf : state.utf.take 8 = state.utf := by simpa only [shape.utf] using (List.take_length (l := state.utf))
  simp only [TlsChatResponse.readState,TlsChatResponse.stateBytes,TlsChatResponse.headerBytes,
    TlsChatResponse.readHeader,TlsWebSocketUpgrade.get]
  simp (disch := omega) [List.getElem?_append,List.drop_append,List.take_append,
    dropModes,dropPositions,dropKinds,dropUtf,dropWord,dropStack,
    takeModes,takePositions,takeKinds,takeUtf,Word64.bytes_length,word_chunks_length,
    shape.modes,shape.positions,shape.kinds,shape.stack,shape.utf,pack_word_bytes]
  simp only [List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  trace_state

end ChatResponseReference.ParserCircuitCandidateV1
