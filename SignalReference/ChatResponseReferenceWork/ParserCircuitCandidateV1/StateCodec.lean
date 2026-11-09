import ChatResponseReferenceWork.ParserCircuitCandidateV1.WordCodec
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.ParserCircuitCandidateV1
set_option maxHeartbeats 2000000

 theorem word_chunks_length (words : List (BitVec 64)) :
    (words.flatMap (Word64.bytes Word64.concrete)).length = 8 * words.length := by
  induction words with
  | nil => rfl
  | cons word rest ih => simp [Word64.bytes_length,ih,Nat.mul_add,Nat.add_comm]

theorem word_chunk (words : List (BitVec 64)) (index : Nat) (bound : index < words.length) :
    ((words.flatMap (Word64.bytes Word64.concrete)).drop (8*index)).take 8 =
    Word64.bytes Word64.concrete words[index] := by
  induction words generalizing index with
  | nil => simp at bound
  | cons word rest ih =>
    cases index with
    | zero => simp [Word64.bytes_length]
    | succ index =>
      have less : index < rest.length := by simpa using bound
      have dropped : (Word64.bytes Word64.concrete word).drop (8+8*index) = [] :=
        List.drop_eq_nil_of_le (by rw [Word64.bytes_length]; omega)
      simpa [List.drop_append,Word64.bytes_length,Nat.mul_add,Nat.add_comm,dropped] using ih index less

theorem pack_word_chunk (words : List (BitVec 64)) (index : Nat) (bound : index < words.length) :
    Word64.concrete.pack (((words.flatMap (Word64.bytes Word64.concrete)).drop (8*index)).take 8) = words[index] := by
  rw [word_chunk words index bound,pack_word_bytes]

theorem word_chunk_suffix (words : List (BitVec 64)) (suffix : List (BitVec 8))
    (index : Nat) (bound : index < words.length) :
    (((words.flatMap (Word64.bytes Word64.concrete)) ++ suffix).drop (8*index)).take 8 =
    Word64.bytes Word64.concrete words[index] := by
  induction words generalizing index with
  | nil => simp at bound
  | cons word rest ih =>
    cases index with
    | zero => simp [Word64.bytes_length]
    | succ index =>
      have less : index < rest.length := by simpa using bound
      have dropped : (Word64.bytes Word64.concrete word).drop (8+8*index) = [] :=
        List.drop_eq_nil_of_le (by rw [Word64.bytes_length]; omega)
      simpa [List.append_assoc,List.drop_append,Word64.bytes_length,Nat.mul_add,Nat.add_comm,dropped] using ih index less

theorem word_chunk_prefix_suffix (beforeBytes suffix : List (BitVec 8)) (words : List (BitVec 64))
    (index : Nat) (bound : index < words.length) :
    ((beforeBytes ++ words.flatMap (Word64.bytes Word64.concrete) ++ suffix).drop
      (beforeBytes.length+8*index)).take 8 = Word64.bytes Word64.concrete words[index] := by
  have dropped : beforeBytes.drop (beforeBytes.length+8*index) = [] := List.drop_eq_nil_of_le (by omega)
  simpa [List.append_assoc,List.drop_append,dropped] using word_chunk_suffix words suffix index bound

theorem decode_word_table (beforeBytes suffix : List (BitVec 8)) (words : List (BitVec 64)) :
    ((List.range words.length).map (fun index => Word64.concrete.pack
      (((beforeBytes ++ words.flatMap (Word64.bytes Word64.concrete) ++ suffix).drop
        (beforeBytes.length+8*index)).take 8))) = words := by
  apply List.ext_getElem (by simp)
  intro index left right
  simp only [List.getElem_map,List.getElem_range]
  rw [word_chunk_prefix_suffix beforeBytes suffix words index right,pack_word_bytes]

structure CodecShape (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) : Prop where
  modes : state.modes.length = 4
  positions : state.positions.length = 10
  kinds : state.kinds.length = 4
  stack : state.stack.length = 100
  utf : state.utf.length = 8

theorem state_bytes_length (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (shape : CodecShape state) :
    (TlsChatResponse.stateBytes Word64.concrete state).length = 932 := by
  simp only [TlsChatResponse.stateBytes,TlsChatResponse.headerBytes,List.length_append,
    List.length_cons,List.length_nil,Word64.bytes_length,word_chunks_length,
    shape.modes,shape.positions,shape.kinds,shape.stack,shape.utf]

def statePrefix (s : TlsChatResponse.State (BitVec 8) (BitVec 64)) : List (BitVec 8) :=
  let o := Word64.concrete
  [s.valid] ++
  [s.seen] ++
  [s.finished] ++
  [s.successful] ++
  s.modes ++
  s.positions ++
  Word64.bytes o s.value ++
  Word64.bytes o s.tag ++
  [s.scalarKnown] ++
  s.kinds ++
  [s.inner] ++
  Word64.bytes o s.responseRemaining ++
  Word64.bytes o s.budget ++
  Word64.bytes o s.skip ++
  Word64.bytes o s.depth

def stateSuffix (s : TlsChatResponse.State (BitVec 8) (BitVec 64)) : List (BitVec 8) :=
  let o := Word64.concrete
  Word64.bytes o s.typeValue ++
  [s.requestPresent] ++
  [s.responsePresent] ++
  [s.idPresent] ++
  Word64.bytes o s.id ++
  Word64.bytes o s.expected ++
  Word64.bytes o s.status ++
  [s.bodyPresent] ++
  Word64.bytes o s.bodyLength ++
  [s.messagePresent] ++
  s.utf ++
  TlsChatResponse.headerBytes s.header

theorem state_bytes_split (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) :
    TlsChatResponse.stateBytes Word64.concrete state =
    statePrefix state ++ state.stack.flatMap (Word64.bytes Word64.concrete) ++ stateSuffix state := by
  simp only [TlsChatResponse.stateBytes,statePrefix,stateSuffix,List.append_assoc]

theorem state_prefix_length (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (shape : CodecShape state) :
    (statePrefix state).length = 72 := by
  simp [statePrefix,Word64.bytes_length,shape.modes,shape.positions,shape.kinds]

theorem decoded_state_stack (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (shape : CodecShape state) :
    (List.range 100).map (fun i => Word64.concrete.pack
      (((TlsChatResponse.stateBytes Word64.concrete state).drop (72+8*i)).take 8)) = state.stack := by
  have table := decode_word_table (statePrefix state) (stateSuffix state) state.stack
  rw [state_prefix_length state shape,shape.stack,←state_bytes_split] at table
  exact table

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
  have takeWord word : (Word64.bytes Word64.concrete word).take 8 = Word64.bytes Word64.concrete word := by
    simpa only [Word64.bytes_length] using (List.take_length (l := Word64.bytes Word64.concrete word))
  have stackSum : (state.stack.map (fun _ => 8)).sum = 800 := by
    have equal := word_chunks_length state.stack
    simpa [Word64.bytes_length,shape.stack] using equal
  simp only [TlsChatResponse.readState]
  rw [decoded_state_stack state shape]
  simp only [TlsChatResponse.stateBytes,TlsChatResponse.headerBytes,
    TlsChatResponse.readHeader,TlsWebSocketUpgrade.get]
  simp (disch := omega) [List.getElem?_append,List.drop_append,List.take_append,
    dropModes,dropPositions,dropKinds,dropUtf,dropWord,dropStack,
    takeModes,takePositions,takeKinds,takeUtf,takeWord,stackSum,Word64.bytes_length,
    shape.modes,shape.positions,shape.kinds,shape.utf,pack_word_bytes]
  simp only [List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]


#print axioms read_encoded_state
#print axioms decoded_state_stack
#print axioms state_bytes_split
#print axioms state_prefix_length
#print axioms word_chunk_suffix
#print axioms word_chunk_prefix_suffix
#print axioms decode_word_table
#print axioms word_chunk
#print axioms pack_word_chunk
#print axioms state_bytes_length
end ChatResponseReference.ParserCircuitCandidateV1
