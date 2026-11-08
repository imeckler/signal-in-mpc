import ProtoParseWork.FullParserV3Work.Numeric.Fields
import ProtoParseWork.ParserErrorStateV2Work.Initialization
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open DispatcherIntegration ParserErrorStateV2
open LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 2000000

theorem initialize_get_general (fields : List (ProtoParse.Field (BitVec 8) (BitVec 64)))
    (tag : BitVec 64) (i : Nat) (hi : i < fields.length) :
    (ProtoParse.initializeFields Word64.concrete ByteAuth.concrete 255 tag fields)[i]'(by
      rw [initialize_length]; exact hi) =
    if tag = BitVec.ofNat 64 (i+1) then
      ProtoParse.selectField Word64.concrete ByteAuth.concrete fields[i].present fields[i] ⟨255,0,0,0⟩
    else fields[i] := by
  simp only [ProtoParse.initializeFields,List.getElem_map,List.getElem_zipIdx,Nat.zero_add,word_eq_value]
  by_cases h : tag = BitVec.ofNat 64 (i+1)
  · have hc : tag = Word64.concrete.const (i+1) := h
    simp only [if_pos hc,if_pos h]
    exact select_full _ _
  · have hc : tag ≠ Word64.concrete.const (i+1) := h
    simp only [if_neg hc,if_neg h]
    exact select_zero _ _

theorem scalar_initialize_view (fields : List (ProtoParse.Field (BitVec 8) (BitVec 64)))
    (tag : BitVec 64) (i : Nat) (hi : i < fields.length)
    (hp : fields[i].present = 0 ∨ fields[i].present = 255) :
    scalarView ((ProtoParse.initializeFields Word64.concrete ByteAuth.concrete 255 tag fields)[i]'(by
      rw [initialize_length]; exact hi)) =
    if tag = BitVec.ofNat 64 (i+1) then some ((scalarView fields[i]).getD 0#u32) else scalarView fields[i] := by
  rw [initialize_get_general]
  split
  · rename_i h
    rw [← initialize_get fields i hi]
    exact scalar_option_initialization fields i hi hp
  · rfl

theorem bytes_initialize_view (body : Slice U8)
    (fields : List (ProtoParse.Field (BitVec 8) (BitVec 64)))
    (tag : BitVec 64) (i : Nat) (hi : i < fields.length)
    (hp : fields[i].present = 0 ∨ fields[i].present = 255) :
    bytesView body ((ProtoParse.initializeFields Word64.concrete ByteAuth.concrete 255 tag fields)[i]'(by
      rw [initialize_length]; exact hi)) =
    if tag = BitVec.ofNat 64 (i+1) then some ((bytesView body fields[i]).getD (alloc.vec.Vec.new U8))
    else bytesView body fields[i] := by
  rw [initialize_get_general]
  split
  · rw [← initialize_get fields i hi]
    exact bytes_option_initialization body fields i hi hp
  · rfl

def messageView (body : Slice U8) (fields : List (ProtoParse.Field (BitVec 8) (BitVec 64)))
    (hl : fields.length = 6) : SignalMessageIntegration.proto.wire.SignalMessage :=
  ⟨bytesView body fields[0], scalarView fields[1], scalarView fields[2],
    bytesView body fields[3],bytesView body fields[4],bytesView body fields[5]⟩

/-- Exact generated dispatcher get-or-insert operation on all six Options. -/
def initializeMessage (tag : BitVec 64) (m : SignalMessageIntegration.proto.wire.SignalMessage) :
    SignalMessageIntegration.proto.wire.SignalMessage :=
  ⟨if tag = 1 then some (m.ratchet_key.getD (alloc.vec.Vec.new U8)) else m.ratchet_key,
   if tag = 2 then some (m.counter.getD 0#u32) else m.counter,
   if tag = 3 then some (m.previous_counter.getD 0#u32) else m.previous_counter,
   if tag = 4 then some (m.ciphertext.getD (alloc.vec.Vec.new U8)) else m.ciphertext,
   if tag = 5 then some (m.pq_ratchet.getD (alloc.vec.Vec.new U8)) else m.pq_ratchet,
   if tag = 6 then some (m.addresses.getD (alloc.vec.Vec.new U8)) else m.addresses⟩

/-- All six fields, including absent/default and existing values, commute with
initialization. The premise is the maintained bit-mask invariant, not primitive
or dispatcher correctness. -/
theorem message_initialize_view (body : Slice U8)
    (fields : List (ProtoParse.Field (BitVec 8) (BitVec 64))) (tag : BitVec 64)
    (hl : fields.length = 6)
    (hp : ∀ i (hi : i < fields.length), fields[i].present = 0 ∨ fields[i].present = 255) :
    messageView body (ProtoParse.initializeFields Word64.concrete ByteAuth.concrete 255 tag fields)
      (by rw [initialize_length,hl]) = initializeMessage tag (messageView body fields hl) := by
  dsimp only [messageView,initializeMessage]
  congr 1
  · exact bytes_initialize_view body fields tag 0 (by omega) (hp 0 (by omega))
  · exact scalar_initialize_view fields tag 1 (by omega) (hp 1 (by omega))
  · exact scalar_initialize_view fields tag 2 (by omega) (hp 2 (by omega))
  · exact bytes_initialize_view body fields tag 3 (by omega) (hp 3 (by omega))
  · exact bytes_initialize_view body fields tag 4 (by omega) (hp 4 (by omega))
  · exact bytes_initialize_view body fields tag 5 (by omega) (hp 5 (by omega))

def replaceMessage (body : Slice U8) (tag : BitVec 64)
    (payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (m : SignalMessageIntegration.proto.wire.SignalMessage) : SignalMessageIntegration.proto.wire.SignalMessage :=
  let field : ProtoParse.Field (BitVec 8) (BitVec 64) := ⟨255,payload.stop,payload.value,payload.value⟩
  ⟨if tag = 1 then bytesView body field else m.ratchet_key,
   if tag = 2 then scalarView field else m.counter,
   if tag = 3 then scalarView field else m.previous_counter,
   if tag = 4 then bytesView body field else m.ciphertext,
   if tag = 5 then bytesView body field else m.pq_ratchet,
   if tag = 6 then bytesView body field else m.addresses⟩

/-- Successful scalar/bytes writes project all six Options, including replacement
of duplicates and empty byte values. No untouched field is dropped. -/
theorem message_write_view (body : Slice U8)
    (fields : List (ProtoParse.Field (BitVec 8) (BitVec 64))) (tag : BitVec 64)
    (payload : ProtoParse.Decoded (BitVec 8) (BitVec 64)) (hl : fields.length = 6) :
    messageView body (ProtoParse.writeFields Word64.concrete ByteAuth.concrete 255 tag payload fields)
      (by simp only [ProtoParse.writeFields,List.length_map,List.length_zipIdx]; exact hl) =
    replaceMessage body tag payload (messageView body fields hl) := by
  dsimp only [messageView,replaceMessage]
  congr 1 <;> rw [LibSignalReference.Candidate.ProstTopField.write_fields_get _ _ _ _ (by omega)]
  all_goals split <;> simp_all

#print axioms message_write_view

#print axioms message_initialize_view

#print axioms initialize_get_general
#print axioms scalar_initialize_view
#print axioms bytes_initialize_view
end FullParserV3
