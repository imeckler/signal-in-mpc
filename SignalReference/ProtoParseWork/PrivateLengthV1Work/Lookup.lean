import ProtoParseWork.PrivateLengthV1Work.Table
import ProtoParseWork.FullParserV3Work.Table
namespace PrivateLengthV1.Lookup
open TlsMpc TlsMpc.Signal
open LibSignalReference.Candidate.ProstSkipKey LibSignalReference.Candidate.ProstTopField

def rows (f : Nat → ProtoParse.Decoded (BitVec 8) (BitVec 64)) (start count : Nat) :=
  (List.range' start count).map f

/-- Empty-prefix rows past the actual end act exactly like lookup's fallback,
for every shared index. Extending the capacity cannot change a lookup. -/
theorem cut (f : Nat → ProtoParse.Decoded (BitVec 8) (BitVec 64)) (ending : Nat)
    (past : ∀ position, ending ≤ position → f position = ⟨0,BitVec.ofNat 64 position,0⟩)
    (count start : Nat) (index : BitVec 64) :
    ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete index start (rows f start count) =
    ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete index start
      (rows f start (min count (ending-start))) := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    by_cases inside : start < ending
    · have clipped : min (count+1) (ending-start) = min count (ending-(start+1))+1 := by omega
      rw [clipped]
      simp only [rows,List.range'_succ,List.map_cons,ProtoParse.lookupDecoded]
      have rest := ih (start+1)
      unfold rows at rest
      rw [rest]
    · have clipped : min (count+1) (ending-start) = 0 := by omega
      have clippedRest : min count (ending-(start+1)) = 0 := by omega
      rw [clipped]
      simp only [rows,List.range'_succ,List.range'_zero,List.map_cons,List.map_nil,ProtoParse.lookupDecoded]
      have rest := ih (start+1)
      rw [clippedRest] at rest
      change ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete index (start+1)
        ((List.range' (start+1) count).map f) = ⟨0,index,0⟩ at rest
      rw [rest,past start (by omega),word_eq_value]
      by_cases equal : index = Word64.concrete.const start
      · rw [if_pos equal,select_decoded_full]
        subst index
        rfl
      · rw [if_neg equal,select_decoded_zero]
        rfl


theorem window_rows (f : Nat → ProtoParse.Decoded (BitVec 8) (BitVec 64)) (capacity start : Nat) :
    (((List.range capacity).map f).drop start).take 10 = rows f start (min 10 (capacity-start)) := by
  apply List.ext_getElem
  · simp [rows]
  · intro index left right
    simp [rows]

theorem payload_lookup (bytes : List (BitVec 8)) (ending start : Nat)
    (inside : ending ≤ bytes.length) (capacity : bytes.length ≤ 512) (index : BitVec 64) :
    ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete index start
      (((PrivateProtoParseV1.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
          (BitVec.ofNat 64 ending) bytes).drop start).take 10) =
    ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete index start
      (((ProtoParse.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
          (bytes.take ending)).drop start).take 10) := by
  let f := ProtoParse.decodePrefix VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (bytes.take ending)
  have past : ∀ position, ending ≤ position → f position = ⟨0,BitVec.ofNat 64 position,0⟩ := by
    intro position beyond
    apply DecoderPadding.prefix_past
    simpa only [List.length_take,Nat.min_eq_left inside] using beyond
  rw [Table.table_eq bytes ending inside capacity]
  simp only [ProtoParse.table,List.length_take,Nat.min_eq_left inside]
  rw [window_rows,window_rows]
  change ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete index start
      (rows f start (min 10 (bytes.length-start))) =
    ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete index start
      (rows f start (min 10 (ending-start)))
  rw [cut f ending past]
  have lengths : min (min 10 (bytes.length-start)) (ending-start) = min 10 (ending-start) := by omega
  rw [lengths]

theorem key_get (bytes : List (BitVec 8)) (ending position : Nat)
    (inside : ending ≤ bytes.length) (capacity : bytes.length ≤ 512) (before : position < ending) :
    (PrivateProtoParseV1.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      (BitVec.ofNat 64 ending) bytes)[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩ =
    (ProtoParse.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      (bytes.take ending))[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩ := by
  rw [Table.table_eq bytes ending inside capacity]
  have withinCapacity : position < bytes.length := by omega
  simp [ProtoParse.table,List.length_take,Nat.min_eq_left inside,List.getElem?_map,
    List.getElem?_range before,List.getElem?_range withinCapacity]


theorem full_lookup (bytes : List (BitVec 8)) (ending : Nat)
    (inside : ending ≤ bytes.length) (capacity : bytes.length ≤ 512) (index : BitVec 64) :
    ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete index 0
      (PrivateProtoParseV1.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
        (BitVec.ofNat 64 ending) bytes) =
    ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete index 0
      (ProtoParse.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (bytes.take ending)) := by
  let f := ProtoParse.decodePrefix VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (bytes.take ending)
  have past : ∀ position, ending ≤ position → f position = ⟨0,BitVec.ofNat 64 position,0⟩ := by
    intro position beyond
    apply DecoderPadding.prefix_past
    simpa only [List.length_take,Nat.min_eq_left inside] using beyond
  rw [Table.table_eq bytes ending inside capacity]
  simp only [ProtoParse.table,List.length_take,Nat.min_eq_left inside]
  simpa only [rows,List.range_eq_range',Nat.sub_zero,Nat.min_eq_right inside] using
    cut f ending past bytes.length 0 index

theorem last_ok (bytes : List (BitVec 8)) (ending : Nat)
    (inside : ending ≤ bytes.length) (capacity : bytes.length ≤ 512) (positive : 0 < ending) :
    (ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete
      (Word64.concrete.sub (BitVec.ofNat 64 ending) (Word64.concrete.const 1)) 0
      (PrivateProtoParseV1.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
        (BitVec.ofNat 64 ending) bytes)).ok =
    ((ProtoParse.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (bytes.take ending))[ending-1]?.getD ⟨0,BitVec.ofNat 64 (ending-1),0⟩).ok := by
  have small : ending < 2^64 := by omega
  have sub : Word64.concrete.sub (BitVec.ofNat 64 ending) (Word64.concrete.const 1) =
      BitVec.ofNat 64 (ending-1) := by
    change BitVec.ofNat 64 ending - (1 : BitVec 64) = _
    have predecessor : BitVec.ofNat 64 ending = BitVec.ofNat 64 (ending-1) + (1 : BitVec 64) := by
      change BitVec.ofNat 64 ending = BitVec.ofNat 64 (ending-1) + BitVec.ofNat 64 1
      rw [←BitVec.ofNat_add]
      congr 1; omega
    rw [predecessor,BitVec.add_sub_cancel]
  rw [sub,full_lookup bytes ending inside capacity]
  let old := ProtoParse.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (bytes.take ending)
  have length : old.length = ending := by simp [old,ProtoParse.table,Nat.min_eq_left inside]
  have atLast : ending-1 < old.length := by omega
  have lookup := lookup_decoded_get old 0 (ending-1) atLast (by omega)
  change (ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete (BitVec.ofNat 64 (ending-1)) 0 old).ok =
    (old[ending-1]?.getD ⟨0,BitVec.ofNat 64 (ending-1),0⟩).ok
  rw [List.getElem?_eq_getElem atLast,Option.getD_some]
  simpa only [Nat.zero_add] using congrArg ProtoParse.Decoded.ok lookup

#print axioms cut
#print axioms payload_lookup
#print axioms key_get
#print axioms last_ok
end PrivateLengthV1.Lookup
