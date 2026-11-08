import ProtoParseWork.FullParserV3Work.DecoderTable
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open LibSignalReference.Candidate.ProstSkipSlice LibSignalReference.Candidate.ProstSkipBuf
open LibSignalReference.Candidate.ProstTopField LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 2000000

/-- A successful actual key establishes every numeric key/cursor invariant
needed by scan transitions; none is supplied as a caller correctness premise. -/
theorem actual_key_row (bytes after : Slice U8) (position : Nat)
    (tag : U32) (kind : LoopSupportSkip.encoding.wire_type.WireType)
    (hp : position < bytes.length)
    (hd : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,kind),after)) :
    let row := (ProtoParse.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes))[position]?.getD
      ⟨0,BitVec.ofNat 64 position,0⟩
    ∃ count, 1 ≤ count ∧ count ≤ 10 ∧ position+count ≤ bytes.length ∧
      after = drop bytes (position+count) ∧ row.ok = 255 ∧
      row.stop = BitVec.ofNat 64 (position+count) ∧ row.value.toNat ≤ 4294967295 ∧
      row.value >>> 3 ≠ 0 ∧
      row.value >>> 3 = BitVec.ofNat 64 tag.val ∧
      row.value &&& 7 = BitVec.ofNat 64 (wireNumber kind) ∧
      (keyFields Word64.concrete ByteAuth.concrete row).ok = 255 := by
  obtain ⟨value,count,hv,htag,hkind,hc,h10,hbound,hrest,hrow⟩ := table_actual_key bytes after position tag kind hp hd
  dsimp only
  rw [List.getElem?_eq_getElem (by rw [table_length]; simpa only [contents,List.length_map] using hp),Option.getD_some,hrow]
  refine ⟨count,hc,h10,hbound,hrest,rfl,rfl,hv.1,?_,?_,?_,?_⟩
  · intro hz
    have hsmall := (shift_zero value.bv).mp hz
    have hlarge := hv.2.1
    rw [UScalar.bv_toNat] at hsmall
    omega
  · apply BitVec.eq_of_toNat_eq
    have hb : tag.val < 2^64 := by have h := hv.1; omega
    simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,UScalar.bv_toNat,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hb]
    exact htag.symm
  · apply BitVec.eq_of_toNat_eq
    have hb : wireNumber kind < 2^64 := by cases kind <;> decide
    simp only [kind_nat,UScalar.bv_toNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hb]
    exact hkind.symm
  · rw [key_mask]
    have hvalid : value.bv.toNat ≤ 4294967295 ∧ 8 ≤ value.bv.toNat ∧ value.bv.toNat % 8 ≤ 5 := by
      simpa only [ValidValue,UScalar.bv_toNat] using hv
    simp only [hvalid,if_true]
    rfl

#print axioms actual_key_row
end FullParserV3
