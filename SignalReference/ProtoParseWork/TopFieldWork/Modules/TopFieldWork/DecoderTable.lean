import TopFieldWork.Scan

namespace LibSignalReference.Candidate.ProstTopField
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
open LibSignalReference.Candidate.ProstSkipSlice LibSignalReference.Candidate.ProstSkipBuf
open LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 500000

 theorem decode_prefix_drop (wire : List (BitVec 8)) (position : Nat) :
    ProtoParse.decodePrefix VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete wire position =
      let row := ProtoParse.decodePrefix VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (wire.drop position) 0
      ⟨row.ok,BitVec.ofNat 64 position + row.stop,row.value⟩ := by
  simp [ProtoParse.decodePrefix,Word64.concrete]

theorem contents_drop (bytes : Slice U8) (position : Nat) :
    contents (drop bytes position) = (contents bytes).drop position := by
  exact List.map_drop

theorem done_index_positive (wire : List (BitVec 8))
    (hd : (VarintDecode.Spqr.decode wire).done = true) :
    1 ≤ (VarintDecode.Spqr.decode wire).index := by
  generalize hf : min 10 wire.length = fuel at *
  cases fuel with
  | zero => simp [VarintDecode.Spqr.decode,hf,VarintDecode.Spqr.run] at hd
  | succ fuel =>
      simp only [VarintDecode.Spqr.decode,hf,VarintDecode.Spqr.run,Bool.false_eq_true,if_false]
      exact (VarintDecode.Spqr.run_index_bounds wire fuel 1 _ _).1

/-- Successful actual prefixes consume at least one byte. This discharges the
lower bound needed by the circuit's ten-entry payload lookup window. -/
theorem prefix_count_positive (bytes : Slice U8) (count : Nat) (value : U64)
    (hc : count ≤ 10)
    (hp : ProtoParse.decodePrefix VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes) 0 =
      ⟨255,BitVec.ofNat 64 count,value.bv⟩) : 1 ≤ count := by
  have hd : (VarintDecode.Spqr.decode (contents bytes)).done = true := by
    by_contra hn
    have hf := prefix_decode_failed (contents bytes) (Bool.eq_false_iff.mpr hn)
    have h := congrArg ProtoParse.Decoded.ok hp
    rw [hf] at h
    change (0#8) = 255 at h
    contradiction
  have h := congrArg ProtoParse.Decoded.stop hp
  rw [prefix_stop_done bytes hd] at h
  have hb := decode_index_bounds bytes
  have hn := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : count < 2^64),
    Nat.mod_eq_of_lt (by omega : (VarintDecode.Spqr.decode (contents bytes)).index < 2^64)] at hn
  have hpos := done_index_positive (contents bytes) hd
  omega

/-- Every successful actual decoder call on a suffix is the exact entry of the
precomputed numeric table, including the absolute secret cursor. -/
theorem table_actual_success (bytes after : Slice U8) (position : Nat) (value : U64)
    (hp : position < bytes.length)
    (hd : LoopSupportSkip.encoding.varint.decode_varint sliceBuf (drop bytes position) =
      Result.ok (.Ok value,after)) :
    ∃ count, 1 ≤ count ∧ count ≤ 10 ∧ position+count ≤ bytes.length ∧
      after = drop bytes (position+count) ∧
      (ProtoParse.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes))[position]'(by
        rw [table_length]; simpa only [contents,List.length_map] using hp) =
        ⟨255,BitVec.ofNat 64 (position+count),value.bv⟩ := by
  obtain ⟨result,rest,hr,hpost,_⟩ := decode_full_reference (drop bytes position)
  rw [hd] at hr
  cases hr
  obtain ⟨count,hbound,h10,hprefix,hrest⟩ := hpost
  have hpos := prefix_count_positive (drop bytes position) count value h10 hprefix
  refine ⟨count,hpos,h10,?_,?_,?_⟩
  · rw [drop_length] at hbound; omega
  · rw [hrest,drop_add]
  · rw [table_get _ _ (by simpa only [contents,List.length_map] using hp)]
    rw [decode_prefix_drop,← contents_drop,hprefix]
    simp only [BitVec.ofNat_add]

 theorem table_actual_error (bytes after : Slice U8) (position : Nat)
    (error : LoopSupportSkip.error.DecodeError) (hp : position < bytes.length)
    (hd : LoopSupportSkip.encoding.varint.decode_varint sliceBuf (drop bytes position) =
      Result.ok (.Err error,after)) :
    ((ProtoParse.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes))[position]'(by
      rw [table_length]; simpa only [contents,List.length_map] using hp)).ok = 0 := by
  obtain ⟨result,rest,hr,hpost,_⟩ := decode_full_reference (drop bytes position)
  rw [hd] at hr
  cases hr
  rw [table_get _ _ (by simpa only [contents,List.length_map] using hp),decode_prefix_drop]
  simpa only [← contents_drop] using hpost.2

/-- Exact successful key entry, preserving actual Prost tag/kind checks. -/
theorem table_actual_key (bytes after : Slice U8) (position : Nat)
    (tag : U32) (kind : LoopSupportSkip.encoding.wire_type.WireType)
    (hp : position < bytes.length)
    (hd : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) =
      Result.ok (.Ok (tag,kind),after)) :
    ∃ value count, ValidValue value ∧ tag.val = value.val / 8 ∧ wireNumber kind = value.val % 8 ∧
      1 ≤ count ∧ count ≤ 10 ∧ position+count ≤ bytes.length ∧
      after = drop bytes (position+count) ∧
      (ProtoParse.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes))[position]'(by
        rw [table_length]; simpa only [contents,List.length_map] using hp) =
        ⟨255,BitVec.ofNat 64 (position+count),value.bv⟩ := by
  obtain ⟨value,count,hv,htag,hkind,hbound,h10,hrest,hprefix⟩ :=
    decode_key_success (drop bytes position) after tag kind hd
  have hpos := prefix_count_positive (drop bytes position) count value h10 hprefix
  refine ⟨value,count,hv,htag,hkind,hpos,h10,?_,?_,?_⟩
  · rw [drop_length] at hbound; omega
  · rw [hrest,drop_add]
  · rw [table_get _ _ (by simpa only [contents,List.length_map] using hp)]
    rw [decode_prefix_drop,← contents_drop,hprefix]
    simp only [BitVec.ofNat_add]

/-- Actual payload success agrees with the ten-row shared lookup used by step;
the key's positive consumed length is now supplied by table_actual_key above. -/
theorem payload_actual_success (bytes after : Slice U8) (position keyCount : Nat) (value : U64)
    (hc : 1 ≤ keyCount) (hc10 : keyCount ≤ 10)
    (hp : position+keyCount < bytes.length) (hb : bytes.length ≤ 2^64)
    (hd : LoopSupportSkip.encoding.varint.decode_varint sliceBuf (drop bytes (position+keyCount)) =
      Result.ok (.Ok value,after)) :
    ∃ count, 1 ≤ count ∧ count ≤ 10 ∧ position+keyCount+count ≤ bytes.length ∧
      after = drop bytes (position+keyCount+count) ∧
      ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete
        (BitVec.ofNat 64 (position+keyCount)) (position+1)
        (((ProtoParse.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes)).drop (position+1)).take 10) =
        ⟨255,BitVec.ofNat 64 (position+keyCount+count),value.bv⟩ := by
  obtain ⟨count,hpos,h10,hbound,hrest,hrow⟩ := table_actual_success bytes after (position+keyCount) value hp hd
  refine ⟨count,hpos,h10,hbound,hrest,?_⟩
  rw [payload_window_get _ position keyCount hc hc10
    (by simpa only [table_length,contents,List.length_map] using hp)
    (by simpa only [table_length,contents,List.length_map] using hb)]
  exact hrow

theorem payload_actual_error (bytes after : Slice U8) (position keyCount : Nat)
    (error : LoopSupportSkip.error.DecodeError)
    (hc : 1 ≤ keyCount) (hc10 : keyCount ≤ 10)
    (hp : position+keyCount < bytes.length) (hb : bytes.length ≤ 2^64)
    (hd : LoopSupportSkip.encoding.varint.decode_varint sliceBuf (drop bytes (position+keyCount)) =
      Result.ok (.Err error,after)) :
    (ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete
      (BitVec.ofNat 64 (position+keyCount)) (position+1)
      (((ProtoParse.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes)).drop (position+1)).take 10)).ok = 0 := by
  rw [payload_window_get _ position keyCount hc hc10
    (by simpa only [table_length,contents,List.length_map] using hp)
    (by simpa only [table_length,contents,List.length_map] using hb)]
  exact table_actual_error bytes after (position+keyCount) error hp hd

#print axioms payload_actual_error
#print axioms table_actual_key
#print axioms payload_actual_success
#print axioms decode_prefix_drop
#print axioms contents_drop
#print axioms done_index_positive
#print axioms prefix_count_positive
#print axioms table_actual_success
#print axioms table_actual_error
end LibSignalReference.Candidate.ProstTopField
