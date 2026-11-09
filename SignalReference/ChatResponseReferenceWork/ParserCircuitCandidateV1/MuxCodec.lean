import ChatResponseReferenceWork.ParserCircuitCandidateV1.StateCodec
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.ParserCircuitCandidateV1

 theorem read_slot_bytes (slot : TlsChatResponseMux.Slot (BitVec 8) (BitVec 64)) :
    TlsChatResponseMux.readSlot Word64.concrete ByteAuth.concrete
      (TlsChatResponseMux.slotBytes Word64.concrete slot) = slot := by
  have takeWord word : (Word64.bytes Word64.concrete word).take 8 = Word64.bytes Word64.concrete word := by
    simpa only [Word64.bytes_length] using (List.take_length (l := Word64.bytes Word64.concrete word))
  simp [TlsChatResponseMux.readSlot,TlsChatResponseMux.slotBytes,TlsWebSocketUpgrade.get,
    takeWord,pack_word_bytes]

 theorem slot_bytes_length (slot : TlsChatResponseMux.Slot (BitVec 8) (BitVec 64)) :
    (TlsChatResponseMux.slotBytes Word64.concrete slot).length = 11 := by
  simp [TlsChatResponseMux.slotBytes,Word64.bytes_length]

 theorem slots_length (slots : List (TlsChatResponseMux.Slot (BitVec 8) (BitVec 64))) :
    (slots.flatMap (TlsChatResponseMux.slotBytes Word64.concrete)).length = 11*slots.length := by
  induction slots with
  | nil => rfl
  | cons slot rest ih => simp [slot_bytes_length,ih,Nat.mul_add,Nat.add_comm]

 theorem slot_chunk_suffix (slots : List (TlsChatResponseMux.Slot (BitVec 8) (BitVec 64)))
    (suffix : List (BitVec 8)) (index : Nat) (bound : index < slots.length) :
    (((slots.flatMap (TlsChatResponseMux.slotBytes Word64.concrete)) ++ suffix).drop (11*index)).take 11 =
    TlsChatResponseMux.slotBytes Word64.concrete slots[index] := by
  induction slots generalizing index with
  | nil => simp at bound
  | cons slot rest ih =>
    cases index with
    | zero => simp [slot_bytes_length]
    | succ index =>
      have less : index < rest.length := by simpa using bound
      have dropped : (TlsChatResponseMux.slotBytes Word64.concrete slot).drop (11+11*index) = [] :=
        List.drop_eq_nil_of_le (by rw [slot_bytes_length]; omega)
      simpa [List.append_assoc,List.drop_append,slot_bytes_length,Nat.mul_add,Nat.add_comm,dropped] using ih index less

 theorem decode_slot_table (beforeBytes suffix : List (BitVec 8))
    (slots : List (TlsChatResponseMux.Slot (BitVec 8) (BitVec 64))) :
    ((List.range slots.length).map (fun index => TlsChatResponseMux.readSlot Word64.concrete ByteAuth.concrete
      (((beforeBytes ++ slots.flatMap (TlsChatResponseMux.slotBytes Word64.concrete) ++ suffix).drop
        (beforeBytes.length+11*index)).take 11))) = slots := by
  apply List.ext_getElem (by simp)
  intro index left right
  simp only [List.getElem_map,List.getElem_range]
  have dropped : beforeBytes.drop (beforeBytes.length+11*index) = [] := List.drop_eq_nil_of_le (by omega)
  have chunk := slot_chunk_suffix slots suffix index right
  simpa [List.append_assoc,List.drop_append,dropped,chunk,read_slot_bytes] using congrArg
    (TlsChatResponseMux.readSlot Word64.concrete ByteAuth.concrete) chunk

structure MuxCodecShape (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64)) : Prop where
  parser : CodecShape state.parser
  slots : state.slots.length = 4
  rows : state.rows.length = 4

theorem decoded_mux_slots (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64)) (shape : MuxCodecShape state) :
    (List.range 4).map (fun i => TlsChatResponseMux.readSlot Word64.concrete ByteAuth.concrete
      (((TlsChatResponseMux.stateBytes Word64.concrete state).drop (933+11*i)).take 11)) = state.slots := by
  have table := decode_slot_table
    ([state.valid] ++ TlsChatResponse.stateBytes Word64.concrete state.parser)
    ([state.queued] ++ state.rows) state.slots
  simp only [List.length_append,List.length_cons,List.length_nil,state_bytes_length state.parser shape.parser,
    shape.slots] at table
  simpa only [TlsChatResponseMux.stateBytes,List.append_assoc] using table

theorem get_at_tail (a : ByteAuth.Ops B) (beforeBytes tailBytes : List B) (index : Nat) :
    TlsWebSocketUpgrade.get a (beforeBytes ++ tailBytes) (beforeBytes.length+index) =
    TlsWebSocketUpgrade.get a tailBytes index := by
  unfold TlsWebSocketUpgrade.get
  rw [List.getElem?_append_right (by omega)]
  simp

theorem rows_from_bytes (a : ByteAuth.Ops B) (rows : List B) :
    (List.range rows.length).map (TlsWebSocketUpgrade.get a rows) = rows := by
  apply List.ext_getElem (by simp)
  intro index left right
  simp [TlsWebSocketUpgrade.get,right]

theorem read_encoded_mux (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64)) (shape : MuxCodecShape state) :
    TlsChatResponseMux.readState Word64.concrete ByteAuth.concrete
      (TlsChatResponseMux.stateBytes Word64.concrete state) = state := by
  have coreLength := state_bytes_length state.parser shape.parser
  have slotLength : (state.slots.flatMap (TlsChatResponseMux.slotBytes Word64.concrete)).length = 44 := by
    rw [slots_length,shape.slots]
  have slotSum : (state.slots.map (fun _ => 11)).sum = 44 := by
    simpa [slot_bytes_length] using slotLength
  have prefixDrop n (bound : 932 ≤ n) : (TlsChatResponse.stateBytes Word64.concrete state.parser).drop n = [] :=
    List.drop_eq_nil_of_le (by rw [coreLength]; exact bound)
  have slotDrop n (bound : 44 ≤ n) : (state.slots.flatMap (TlsChatResponseMux.slotBytes Word64.concrete)).drop n = [] :=
    List.drop_eq_nil_of_le (by rw [slotLength]; exact bound)
  have takeCore : (TlsChatResponse.stateBytes Word64.concrete state.parser).take 932 =
      TlsChatResponse.stateBytes Word64.concrete state.parser := by
    simpa only [coreLength] using (List.take_length (l := TlsChatResponse.stateBytes Word64.concrete state.parser))
  have rows : (List.range 4).map (fun i => TlsWebSocketUpgrade.get ByteAuth.concrete
      (TlsChatResponseMux.stateBytes Word64.concrete state) (978+i)) = state.rows := by
    have frontLength : (([state.valid] ++ TlsChatResponse.stateBytes Word64.concrete state.parser ++
        state.slots.flatMap (TlsChatResponseMux.slotBytes Word64.concrete)) ++ [state.queued]).length = 978 := by
      simp only [List.length_append,List.length_cons,List.length_nil,coreLength,slotLength]
    have rowEq : ∀ i, TlsWebSocketUpgrade.get ByteAuth.concrete
        (TlsChatResponseMux.stateBytes Word64.concrete state) (978+i) =
        TlsWebSocketUpgrade.get ByteAuth.concrete state.rows i := by
      intro i
      rw [←frontLength]
      exact get_at_tail ByteAuth.concrete _ _ i
    simp only [rowEq]
    rw [←shape.rows]
    exact rows_from_bytes _ _
  simp only [TlsChatResponseMux.readState]
  rw [decoded_mux_slots state shape,rows]
  simp only [TlsChatResponseMux.stateBytes,TlsWebSocketUpgrade.get]
  simp [List.getElem?_append,List.drop_append,List.take_append,coreLength,slotLength,slotSum,prefixDrop,slotDrop,
    takeCore,read_encoded_state state.parser shape.parser]

#print axioms decoded_mux_slots
#print axioms read_encoded_mux
#print axioms read_slot_bytes
#print axioms decode_slot_table
end ChatResponseReference.ParserCircuitCandidateV1
