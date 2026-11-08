import ProtoParseWork.PrivateLengthV1Work.Padding
namespace PrivateLengthV1.DecoderPadding
open TlsMpc TlsMpc.Signal

theorem count_bound (bytes : List (BitVec 8)) :
    (OpenResult.get ByteAuth.concrete
      (VarintDecode.Spqr.decodeCore VarintDecode.Spqr.concrete ByteAuth.concrete bytes) 1).toNat ≤
      min 10 bytes.length := by
  have bound := (VarintDecode.Spqr.run_index_bounds bytes (min 10 bytes.length) 0 0 false).2
  simp only [Nat.zero_add] at bound
  change (VarintDecode.Spqr.decode bytes).index ≤ min 10 bytes.length at bound
  have small : (VarintDecode.Spqr.decode bytes).index < 256 := by omega
  rw [VarintDecode.Spqr.decodeCore_spec]
  unfold VarintDecode.Spqr.encodeResult
  split
  · simpa [OpenResult.get,Nat.mod_eq_of_lt small] using bound
  · simp [OpenResult.get]

/-- Appended continuation sentinels preserve the complete decoded row, not
only acceptance. The native uint64 tenth-byte overflow check is retained. -/
theorem prefix_zero (bytes : List (BitVec 8)) (count : Nat) :
    ProtoParse.decodePrefix VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      (bytes++List.replicate count 128) 0 =
    ProtoParse.decodePrefix VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete bytes 0 := by
  have core := Padding.decodeCore_sentinel bytes count
  unfold ProtoParse.decodePrefix
  simp only [List.drop_zero]
  rw [core]
  by_cases long : 10 ≤ bytes.length
  · have ninth : OpenResult.get ByteAuth.concrete (bytes++List.replicate count 128) 9 =
        OpenResult.get ByteAuth.concrete bytes 9 := by
      simp [OpenResult.get,List.getElem?_append_left,show 9 < bytes.length by omega]
    rw [ninth]
  · have short : bytes.length < 10 := by omega
    have bound := count_bound bytes
    have neq : OpenResult.get ByteAuth.concrete
        (VarintDecode.Spqr.decodeCore VarintDecode.Spqr.concrete ByteAuth.concrete bytes) 1 ≠
        ByteAuth.concrete.const 10 := by
      intro equal
      rw [equal] at bound
      change 10 ≤ min 10 bytes.length at bound
      omega
    have notzero : ByteAuth.concrete.not (0 : BitVec 8) = 255 := rfl
    have borall (x : BitVec 8) : Word64.bor ByteAuth.concrete 255 x = 255 := by
      simp [Word64.bor,ByteAuth.concrete,BitVec.xor_assoc]
    simp only [ByteAuth.eqMask_value,if_neg neq,notzero,borall]


theorem prefix_drop (bytes : List (BitVec 8)) (position : Nat) :
    ProtoParse.decodePrefix VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete bytes position =
      let row := ProtoParse.decodePrefix VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (bytes.drop position) 0
      ⟨row.ok,BitVec.ofNat 64 position + row.stop,row.value⟩ := by
  simp [ProtoParse.decodePrefix,Word64.concrete]

/-- Every table row is unaffected by appended continuation padding, including
rows at and beyond the true end and rejection rows with no terminator. -/
theorem prefix_all (bytes : List (BitVec 8)) (count position : Nat) :
    ProtoParse.decodePrefix VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      (bytes++List.replicate count 128) position =
    ProtoParse.decodePrefix VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete bytes position := by
  rw [prefix_drop (bytes++List.replicate count 128) position,prefix_drop bytes position]
  simp only [List.drop_append,List.drop_replicate]
  rw [prefix_zero]


theorem prefix_empty (position : Nat) :
    ProtoParse.decodePrefix VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete [] position =
      ⟨0,BitVec.ofNat 64 position,0⟩ := by
  have zero : ProtoParse.decodePrefix VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete [] 0 =
      ⟨0,0,0⟩ := rfl
  rw [prefix_drop [] position]
  simp only [List.drop_nil,zero]
  exact congrArg (fun stop => (⟨0,stop,0⟩ : ProtoParse.Decoded (BitVec 8) (BitVec 64))) (BitVec.add_zero _)

theorem prefix_past (bytes : List (BitVec 8)) (position : Nat) (past : bytes.length ≤ position) :
    ProtoParse.decodePrefix VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete bytes position =
      ⟨0,BitVec.ofNat 64 position,0⟩ := by
  rw [prefix_drop bytes position,List.drop_eq_nil_of_le past,prefix_empty 0]
  simp

#print axioms count_bound
#print axioms prefix_zero
#print axioms prefix_all
#print axioms prefix_past
end PrivateLengthV1.DecoderPadding
