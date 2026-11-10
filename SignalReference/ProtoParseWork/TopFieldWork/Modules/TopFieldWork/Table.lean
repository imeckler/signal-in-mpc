import TopFieldWork.TopPlan

namespace LibSignalReference.Candidate.ProstTopField
open TlsMpc TlsMpc.Signal
open LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 500000

theorem select_decoded_full (yes no : ProtoParse.Decoded (BitVec 8) (BitVec 64)) :
    ProtoParse.selectDecoded Word64.concrete ByteAuth.concrete 255 yes no = yes := by
  cases yes
  simp only [ProtoParse.selectDecoded,Word64.select_accept]
  simp [Unpad.chooseByte,ByteAuth.concrete,BitVec.xor_assoc]

theorem select_decoded_zero (yes no : ProtoParse.Decoded (BitVec 8) (BitVec 64)) :
    ProtoParse.selectDecoded Word64.concrete ByteAuth.concrete 0 yes no = no := by
  cases no
  simp [ProtoParse.selectDecoded,Word64.concrete,Unpad.chooseByte,ByteAuth.concrete]
  simp only [show (18446744073709551615#64) = BitVec.allOnes 64 by rfl,BitVec.allOnes_and,and_self]

/-- The shared lookup returns exactly its indexed decoder entry; the explicit
64-bit bound excludes modular aliases between public positions. -/
theorem lookup_decoded_get (rows : List (ProtoParse.Decoded (BitVec 8) (BitVec 64)))
    (start index : Nat) (hi : index < rows.length) (hb : start + rows.length ≤ 2^64) :
    ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete
      (BitVec.ofNat 64 (start+index)) start rows = rows[index] := by
  induction rows generalizing start index with
  | nil => simp at hi
  | cons x xs ih =>
    cases index with
    | zero =>
      simp only [Nat.add_zero,ProtoParse.lookupDecoded,word_eq_value,List.getElem_cons_zero]
      have he : BitVec.ofNat 64 start = Word64.concrete.const start := rfl
      rw [if_pos he,select_decoded_full]
    | succ index =>
      have hi' : index < xs.length := by simpa using hi
      have hs : start < 2^64 := by simp only [List.length_cons] at hb; omega
      have hx : start+(index+1) < 2^64 := by simp only [List.length_cons] at hb; omega
      have hn : BitVec.ofNat 64 (start+(index+1)) ≠ Word64.concrete.const start := by
        intro he
        have hh := congrArg BitVec.toNat he
        change (start+(index+1)) % 2^64 = start % 2^64 at hh
        rw [Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hs] at hh
        omega
      simp only [ProtoParse.lookupDecoded,word_eq_value,List.getElem_cons_succ,if_neg hn]
      rw [select_decoded_zero]
      have next := ih (start+1) index hi' (by simp only [List.length_cons] at hb; omega)
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using next

theorem table_length (wire : List (BitVec 8)) :
    (ProtoParse.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete wire).length = wire.length := by
  simp [ProtoParse.table]

theorem table_get (wire : List (BitVec 8)) (position : Nat) (hp : position < wire.length) :
    (ProtoParse.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete wire)[position]'(by
      rw [table_length]; exact hp) =
      ProtoParse.decodePrefix VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete wire position := by
  simp [ProtoParse.table]

/-- The ten-entry payload window used by step contains the decoder at the
secret end of a successful key (one through ten bytes). -/
theorem payload_window_get (rows : List (ProtoParse.Decoded (BitVec 8) (BitVec 64)))
    (position count : Nat) (hc : 1 ≤ count) (hc10 : count ≤ 10)
    (hp : position+count < rows.length) (hb : rows.length ≤ 2^64) :
    ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete
      (BitVec.ofNat 64 (position+count)) (position+1) ((rows.drop (position+1)).take 10) =
      rows[position+count] := by
  have hi : count-1 < ((rows.drop (position+1)).take 10).length := by
    simp only [List.length_take,List.length_drop]; omega
  have hbound : position+1+((rows.drop (position+1)).take 10).length ≤ 2^64 := by
    simp only [List.length_take,List.length_drop]; omega
  have he : position+count = (position+1)+(count-1) := by omega
  have hget := lookup_decoded_get ((rows.drop (position+1)).take 10) (position+1) (count-1) hi hbound
  simpa only [List.getElem_take,List.getElem_drop,← he] using hget

/-- End-of-buffer and beyond-window lookups return an invalid row with the
original cursor; they never accidentally match an aliased 64-bit position. -/
theorem lookup_decoded_past (rows : List (ProtoParse.Decoded (BitVec 8) (BitVec 64)))
    (start index : Nat) (hi : start+rows.length ≤ index) (hb : index < 2^64) :
    ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete
      (BitVec.ofNat 64 index) start rows = ⟨0,BitVec.ofNat 64 index,0⟩ := by
  induction rows generalizing start with
  | nil => rfl
  | cons x xs ih =>
      have hs : start < index := by simp only [List.length_cons] at hi; omega
      have hn : BitVec.ofNat 64 index ≠ Word64.concrete.const start := by
        intro he
        have h := congrArg BitVec.toNat he
        change index % 2^64 = start % 2^64 at h
        rw [Nat.mod_eq_of_lt hb,Nat.mod_eq_of_lt (by omega : start < 2^64)] at h
        omega
      simp only [ProtoParse.lookupDecoded,word_eq_value,if_neg hn,select_decoded_zero]
      exact ih (start+1) (by simp only [List.length_cons] at hi; omega)

theorem payload_window_end (rows : List (ProtoParse.Decoded (BitVec 8) (BitVec 64)))
    (position : Nat) (hp : position < rows.length) (hb : rows.length < 2^64) :
    ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete
      (BitVec.ofNat 64 rows.length) (position+1) ((rows.drop (position+1)).take 10) =
      ⟨0,BitVec.ofNat 64 rows.length,0⟩ := by
  apply lookup_decoded_past _ _ _ _ hb
  simp only [List.length_take,List.length_drop]
  omega

#print axioms lookup_decoded_past
#print axioms payload_window_end
#print axioms select_decoded_full
#print axioms select_decoded_zero
#print axioms lookup_decoded_get
#print axioms table_length
#print axioms table_get
#print axioms payload_window_get
end LibSignalReference.Candidate.ProstTopField
