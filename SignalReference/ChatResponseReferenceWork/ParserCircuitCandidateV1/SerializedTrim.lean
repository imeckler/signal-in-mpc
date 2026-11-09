import ChatResponseReferenceWork.ParserCircuitCandidateV1.MuxCodecShape
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.ParserCircuitCandidateV1

theorem get_slice (a : ByteAuth.Ops B) (raw : List B) (start size index : Nat) (bound : index < size) :
    TlsWebSocketUpgrade.get a ((raw.drop start).take size) index =
    TlsWebSocketUpgrade.get a raw (start+index) := by
  simp [TlsWebSocketUpgrade.get,List.getElem?_drop,bound]

theorem get_word_chunk (words : List (BitVec 64)) (index : Nat) (bound : index < 8*words.length) :
    TlsWebSocketUpgrade.get ByteAuth.concrete (words.flatMap (Word64.bytes Word64.concrete)) index =
    TlsWebSocketUpgrade.get ByteAuth.concrete (Word64.bytes Word64.concrete words[index/8]) (index%8) := by
  have divided : index/8 < words.length := by omega
  have chunk := congrArg (fun raw => TlsWebSocketUpgrade.get ByteAuth.concrete raw (index%8))
    (word_chunk words (index/8) divided)
  rw [get_slice ByteAuth.concrete _ _ _ _ (by omega)] at chunk
  have together : 8*(index/8)+index%8 = index := by omega
  rw [together] at chunk
  exact chunk

theorem get_trimmed_word_byte (word : BitVec 64) (index : Nat) (bound : index < 8) :
    TlsWebSocketUpgrade.get ByteAuth.concrete (Word64.bytes Word64.concrete (trimWord word)) index =
    if index < 4 then 0 else TlsWebSocketUpgrade.get ByteAuth.concrete (Word64.bytes Word64.concrete word) index := by
  have cases : index=0 ∨ index=1 ∨ index=2 ∨ index=3 ∨ index=4 ∨ index=5 ∨ index=6 ∨ index=7 := by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [trimmed_word_bytes,TlsWebSocketUpgrade.get]

theorem get_trimmed_word_chunk (words : List (BitVec 64)) (index : Nat) (bound : index < 8*words.length) :
    TlsWebSocketUpgrade.get ByteAuth.concrete
      ((words.map trimWord).flatMap (Word64.bytes Word64.concrete)) index =
    if index%8 < 4 then 0 else
      TlsWebSocketUpgrade.get ByteAuth.concrete (words.flatMap (Word64.bytes Word64.concrete)) index := by
  rw [get_word_chunk _ index (by simpa only [List.length_map] using bound)]
  simp only [List.getElem_map]
  rw [get_trimmed_word_byte _ _ (by omega),get_word_chunk words index bound]

theorem get_appended (a : ByteAuth.Ops B) (beforeBytes tailBytes : List B) (index : Nat) :
    TlsWebSocketUpgrade.get a (beforeBytes ++ tailBytes) index =
    if index < beforeBytes.length then TlsWebSocketUpgrade.get a beforeBytes index
    else TlsWebSocketUpgrade.get a tailBytes (index-beforeBytes.length) := by
  unfold TlsWebSocketUpgrade.get
  rw [List.getElem?_append]
  split <;> rfl

theorem serialized_layout_trim (beforeBytes afterBytes : List (BitVec 8)) (words : List (BitVec 64))
    (beforeLength : beforeBytes.length = 73) (wordLength : words.length = 100) (index : Nat) :
    TlsWebSocketUpgrade.get ByteAuth.concrete
      (beforeBytes ++ (words.map trimWord).flatMap (Word64.bytes Word64.concrete) ++ afterBytes) index =
    projectedByte ByteAuth.concrete
      (beforeBytes ++ words.flatMap (Word64.bytes Word64.concrete) ++ afterBytes) index := by
  by_cases first : index < 73
  · simp [projectedByte,expandedSourceIndex,first,List.append_assoc,get_appended,beforeLength]
  · by_cases second : index < 873
    · have within : index-73 < 8*words.length := by rw [wordLength]; omega
      have within800 : index-73 < 800 := by omega
      simp only [List.append_assoc,get_appended,List.length_map,word_chunks_length,beforeLength,wordLength,
        first,if_false,within800,if_pos,projectedByte,expandedSourceIndex,second]
      have trim := get_trimmed_word_chunk words (index-73) within
      by_cases high : (index-73)%8 < 4 <;> simpa [ByteAuth.concrete,high] using trim
    · have outside : ¬index-73 < 800 := by omega
      simp only [projectedByte,expandedSourceIndex,first,second,if_false,List.append_assoc,get_appended,
        beforeLength,word_chunks_length,List.length_map,wordLength,outside]

def muxStatePrefix (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64)) : List (BitVec 8) :=
  [state.valid] ++ statePrefix state.parser

def muxStateSuffix (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64)) : List (BitVec 8) :=
  stateSuffix state.parser ++ state.slots.flatMap (TlsChatResponseMux.slotBytes Word64.concrete) ++ [state.queued] ++ state.rows

theorem mux_bytes_layout (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64)) :
    TlsChatResponseMux.stateBytes Word64.concrete state =
    muxStatePrefix state ++ state.parser.stack.flatMap (Word64.bytes Word64.concrete) ++ muxStateSuffix state := by
  simp only [TlsChatResponseMux.stateBytes,state_bytes_split,muxStatePrefix,muxStateSuffix,List.append_assoc]

theorem mux_bytes_length (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64)) (shape : MuxCodecShape state) :
    (TlsChatResponseMux.stateBytes Word64.concrete state).length = 982 := by
  simp only [TlsChatResponseMux.stateBytes,List.length_append,List.length_cons,List.length_nil,
    state_bytes_length state.parser shape.parser,slots_length,shape.slots,shape.rows]

theorem serialized_mux_trim_get (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (shape : MuxCodecShape state) (suffix : List (BitVec 8)) (index : Nat) :
    TlsWebSocketUpgrade.get ByteAuth.concrete
      (TlsChatResponseMux.stateBytes Word64.concrete (trimMuxState state) ++ suffix) index =
    projectedByte ByteAuth.concrete (TlsChatResponseMux.stateBytes Word64.concrete state ++ suffix) index := by
  have beforeLength : (muxStatePrefix state).length = 73 := by
    simp only [muxStatePrefix,List.length_append,List.length_cons,List.length_nil,state_prefix_length state.parser shape.parser]
  have layout := serialized_layout_trim (muxStatePrefix state) (muxStateSuffix state ++ suffix)
    state.parser.stack beforeLength shape.parser.stack index
  rw [mux_bytes_layout,mux_bytes_layout]
  have beforeEq : muxStatePrefix (trimMuxState state) = muxStatePrefix state := rfl
  have afterEq : muxStateSuffix (trimMuxState state) = muxStateSuffix state := rfl
  have stackEq : (trimMuxState state).parser.stack = state.parser.stack.map trimWord := rfl
  simpa only [List.append_assoc,beforeEq,afterEq,stackEq] using layout

theorem expanded_compact_event_output (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (shape : MuxCodecShape state) (flags : List (BitVec 8)) (flagLength : flags.length = 3) :
    (expandInput ByteAuth.concrete (compactOutput ByteAuth.concrete
      (TlsChatResponseMux.stateBytes Word64.concrete state ++ flags))).take 985 =
    TlsChatResponseMux.stateBytes Word64.concrete (trimMuxState state) ++ flags := by
  have leftLength : ((expandInput ByteAuth.concrete (compactOutput ByteAuth.concrete
      (TlsChatResponseMux.stateBytes Word64.concrete state ++ flags))).take 985).length = 985 := by
    simp only [List.length_take,expand_length]
    rfl
  have rightLength : (TlsChatResponseMux.stateBytes Word64.concrete (trimMuxState state) ++ flags).length = 985 := by
    rw [List.length_append,mux_bytes_length _ (mux_trim_codec_shape state shape),flagLength]
  apply List.ext_getElem (leftLength.trans rightLength.symm)
  intro index left right
  have bound : index < 985 := by simpa only [leftLength] using left
  have eq := (expand_compact_get ByteAuth.concrete
    (TlsChatResponseMux.stateBytes Word64.concrete state ++ flags) index bound).trans
    (serialized_mux_trim_get state shape flags index).symm
  have takeEq := get_slice ByteAuth.concrete
    (expandInput ByteAuth.concrete (compactOutput ByteAuth.concrete
      (TlsChatResponseMux.stateBytes Word64.concrete state ++ flags))) 0 985 index bound
  simp only [List.drop_zero,Nat.zero_add] at takeEq
  rw [←takeEq] at eq
  simpa only [TlsWebSocketUpgrade.get,List.getElem?_eq_getElem left,List.getElem?_eq_getElem right,Option.getD_some] using eq

#print axioms mux_bytes_layout
#print axioms serialized_mux_trim_get
#print axioms expanded_compact_event_output
#print axioms serialized_layout_trim
#print axioms get_word_chunk
#print axioms get_trimmed_word_byte
#print axioms get_trimmed_word_chunk
end ChatResponseReference.ParserCircuitCandidateV1
