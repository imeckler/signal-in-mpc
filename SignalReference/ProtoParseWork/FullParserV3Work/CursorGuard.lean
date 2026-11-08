import ProtoParseWork.FullParserV3Work.DecoderTable
import ProtoParseWork.ParserErrorStateV2Work.LastByte
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open LibSignalReference.Candidate.ProstSkipSlice LibSignalReference.Candidate.ProstSkipBuf
open LibSignalReference.Candidate.ProstTopField
set_option maxHeartbeats 1000000

theorem last_byte_drop (bytes : Slice U8) (position : Nat) (hp : position < bytes.length) :
    byte (drop bytes position) ((drop bytes position).length-1) = byte bytes (bytes.length-1) := by
  rw [drop_length]
  simp only [byte,drop,List.getElem?_drop]
  have he : position + (bytes.length-position-1) = bytes.length-1 := by omega
  rw [he]

theorem fast_guard_drop (bytes : Slice U8) (position : Nat) (hp : position < bytes.length) :
    FastGuard (drop bytes position) ↔ bytes.length > position+10 ∨ (byte bytes (bytes.length-1)).val < 128 := by
  unfold FastGuard
  rw [last_byte_drop bytes position hp,drop_length]
  omega

/-- The shared last table row is precisely the actual fast-dispatch guard bit,
without any whole-input decoder correctness hypothesis. -/
theorem table_last_clear (wire : List (BitVec 8)) (hn : 0 < wire.length) :
    ((ProtoParse.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete wire)[wire.length-1]'(by
      rw [table_length]; omega)).ok = if wire[wire.length-1].toNat < 128 then 255 else 0 := by
  rw [table_get _ _ (by omega),decode_prefix_drop]
  have hd : wire.drop (wire.length-1) = [wire[wire.length-1]] := by
    rw [List.drop_eq_getElem_cons (by omega)]
    have he : wire.length-1+1 = wire.length := by omega
    rw [he,List.drop_length]
  rw [hd]
  exact ParserErrorStateV2.last_byte_clear _

theorem table_last_clear_slice (bytes : Slice U8) (hn : 0 < bytes.length) :
    ((ProtoParse.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes))[bytes.length-1]?.getD
      ⟨0,BitVec.ofNat 64 (bytes.length-1),0⟩).ok =
    if (byte bytes (bytes.length-1)).val < 128 then 255 else 0 := by
  have hl : (contents bytes).length = bytes.length := List.length_map _
  have h := table_last_clear (contents bytes) (by omega)
  simp only [hl] at h
  have hb := contents_get bytes (bytes.length-1)
  simp only [List.getElem?_eq_getElem (by omega : bytes.length-1 < (contents bytes).length),Option.getD_some] at hb
  rw [hb,UScalar.bv_toNat] at h
  rw [List.getElem?_eq_getElem (by rw [table_length,hl]; omega),Option.getD_some]
  exact h

theorem key_fast_mask (bytes : Slice U8) (position : Nat) (hp : position < bytes.length) :
    (if bytes.length > position+10 then (255 : BitVec 8) else
      ((ProtoParse.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes))[bytes.length-1]?.getD
        ⟨0,BitVec.ofNat 64 (bytes.length-1),0⟩).ok) =
    if FastGuard (drop bytes position) then 255 else 0 := by
  rw [table_last_clear_slice bytes (by omega)]
  simp only [fast_guard_drop bytes position hp]
  by_cases hg : bytes.length > position+10
  · simp only [hg,true_or,if_true]
  · simp only [hg,false_or,if_false]

#print axioms table_last_clear_slice
#print axioms key_fast_mask

#print axioms last_byte_drop
#print axioms fast_guard_drop
#print axioms table_last_clear
end FullParserV3
