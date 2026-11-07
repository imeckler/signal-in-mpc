import SpqrReference.VarintReference
import ProstEncodingWork.CircuitBridge
import TlsMpc.Signal.Varint64

namespace LibSignalReference.Candidate.SpqrVarint

open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
open LibSignalReference.Candidate.ProstEncoding

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem group_value (word : BitVec 64) (index : Nat) (hi : index < 10) :
    OpenResult.get ByteAuth.concrete (Varint64.groups Varint64.concrete word) index =
      BitVec.ofNat 8 (word.toNat / 128 ^ index % 128) := by
  simp only [Varint64.groups, OpenResult.get, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some, Varint64.concrete, ByteAuth.concrete]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  have hm (n : Nat) : n &&& 127 = n % 128 := by
    simpa using Nat.and_two_pow_sub_one_eq_mod n 7
  change ((word.toNat / 2 ^ (7 * index)) % 256 &&& 127) =
    (word.toNat / 128 ^ index % 128) % 256
  simp only [hm]
  have hp : 2 ^ (7 * index) = 128 ^ index := by rw [Nat.pow_mul]
  rw [hp]
  omega

theorem groups_values (word : BitVec 64) :
    Varint64.groups Varint64.concrete word =
      (List.range 10).map (fun index => BitVec.ofNat 8 (word.toNat / 128 ^ index % 128)) := by
  unfold Varint64.groups
  apply List.map_congr_left
  intro index hi
  have hb := List.mem_range.mp hi
  simpa only [Varint64.groups, OpenResult.get, List.getElem?_map, List.getElem?_range hb,
    Option.map_some, Option.getD_some] using group_value word index hb

theorem groups_naturals (word : BitVec 64) :
    (Varint64.groups Varint64.concrete word).map BitVec.toNat =
      (List.range 10).map (fun index => word.toNat / 128 ^ index % 128) := by
  rw [groups_values, List.map_map]
  apply List.map_congr_left
  intro index hi
  simp only [Function.comp_def, BitVec.toNat_ofNat]
  omega

theorem canonical_width_bounds (word : BitVec 64) (width : Nat)
    (hw1 : 1 ≤ width) (hw10 : width ≤ 10)
    (canonical : Varint64.canonicalGroups (Varint64.groups Varint64.concrete word) width) :
    word.toNat < 128 ^ width ∧ (width = 1 ∨ 128 ^ (width - 1) ≤ word.toNat) := by
  have hz := congrArg (List.map BitVec.toNat) canonical.1
  simp only [List.map_drop, List.map_replicate, groups_naturals] at hz
  have ht : width = 1 ∨ word.toNat / 128 ^ (width - 1) % 128 ≠ 0 := by
    rcases canonical.2 with h | h
    · exact Or.inl h
    · right
      intro hn
      apply h
      rw [group_value word (width - 1) (by omega), hn]
      rfl
  have hword : word.toNat < 18446744073709551616 := word.isLt
  have hw : width = 1 ∨ width = 2 ∨ width = 3 ∨ width = 4 ∨ width = 5 ∨
      width = 6 ∨ width = 7 ∨ width = 8 ∨ width = 9 ∨ width = 10 := by omega
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [List.range_succ] at hz ht ⊢ <;> omega

theorem encode_fixed (word : BitVec 64) (width : Nat) (hw : width ≤ 10) :
    Varint64.encode Varint64.concrete ByteAuth.concrete word width = fixedBytes word.toNat width := by
  unfold Varint64.encode Varint.encodeGroups fixedBytes
  apply List.map_congr_left
  intro index hi
  have hb := List.mem_range.mp hi
  rw [group_value word index (by omega)]
  by_cases hc : index + 1 < width
  · simpa only [if_pos hc, ByteAuth.concrete] using
      byte_xor_continuation (word.toNat / 128 ^ index % 128) (by omega)
  · simp only [if_neg hc, ByteAuth.concrete, BitVec.xor_zero, Nat.add_zero]

theorem encode_publicNat (word : BitVec 64) (width : Nat) (hw1 : 1 ≤ width) (hw10 : width ≤ 10)
    (canonical : Varint64.canonicalGroups (Varint64.groups Varint64.concrete word) width) :
    Varint64.encode Varint64.concrete ByteAuth.concrete word width =
      Varint.publicNat ByteAuth.concrete word.toNat := by
  obtain ⟨upper, lower⟩ := canonical_width_bounds word width hw1 hw10 canonical
  rw [encode_fixed word width hw10, Varint.publicNat]
  exact (publicNatLoop_fixed 10 width word.toNat hw1 hw10 upper lower).symm

theorem accepts_canonical (word : BitVec 64) (width : Nat)
    (accepted : Varint64.accepts Varint64.concrete ByteAuth.concrete word width = 255#8) :
    Varint64.canonicalGroups (Varint64.groups Varint64.concrete word) width := by
  unfold Varint64.accepts at accepted
  rw [Varint64.widthMask_value] at accepted
  split at accepted
  · assumption
  · contradiction

/-- Every U64, every accepted public width, and every buffer within the model's
size bound: actual SPQR pushes exactly the bytes emitted by our circuit. -/
theorem encode_uint64 (value : U64) (width : Nat) (hw1 : 1 ≤ width) (hw10 : width ≤ 10)
    (canonical : Varint64.canonicalGroups (Varint64.groups Varint64.concrete value.bv) width)
    (buf : alloc.vec.Vec U8) (hsize : buf.length + 10 ≤ Usize.max) :
    ∃ after, _root_.SpqrReference.encode_varint value buf = .ok after ∧
      vecContents after = vecContents buf ++ Varint64.encode Varint64.concrete ByteAuth.concrete value.bv width := by
  obtain ⟨after, ha, hv⟩ := encode_appends value buf hsize
  refine ⟨after, ha, ?_⟩
  exact hv.trans (congrArg (fun bytes => vecContents buf ++ bytes)
    (encode_publicNat value.bv width hw1 hw10 canonical).symm)

theorem uint64_refines_artifact (value : U64) (width : Nat) (hw1 : 1 ≤ width) (hw10 : width ≤ 10)
    (canonical : Varint64.canonicalGroups (Varint64.groups Varint64.concrete value.bv) width)
    (buf : alloc.vec.Vec U8) (hsize : buf.length + 10 ≤ Usize.max)
    (secret : _root_.Std.Tactic.BVDecide.BVExpr 64)
    (assign : _root_.Std.Tactic.BVDecide.BVExpr.Assignment)
    (hsecret : secret.eval assign = value.bv) :
    ∃ after, _root_.SpqrReference.encode_varint value buf = .ok after ∧
      ∀ (index : Nat)
        (hi : index < 8 * (Varint64.encode Varint64.symbolic ByteAuth.symbolic secret width).length),
        AigExport.evalRef
          (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
            (Varint64.encode Varint64.symbolic ByteAuth.symbolic secret width))).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
            (Varint64.encode Varint64.symbolic ByteAuth.symbolic secret width))).vec.get index hi)) =
          (ByteCircuit.joinValue ((vecContents after).drop (vecContents buf).length)).getLsbD index := by
  obtain ⟨after, ha, hv⟩ := encode_uint64 value width hw1 hw10 canonical buf hsize
  have written : (vecContents after).drop (vecContents buf).length =
      Varint64.encode Varint64.concrete ByteAuth.concrete value.bv width := by
    rw [hv]
    simp
  refine ⟨after, ha, ?_⟩
  intro index hi
  rw [Varint64.compiled_encode_correct, hsecret]
  exact congrArg (fun bytes => (ByteCircuit.joinValue bytes).getLsbD index) written.symm

/-- SPQR's same U64 helper also agrees with the existing uint32 circuit on
the widened message index used by Message.serialize. -/
theorem encode_uint32 (value : U32) (width : Nat) (hw1 : 1 ≤ width) (hw5 : width ≤ 5)
    (canonical : Varint.canonicalGroups (Varint.groups Sha256.concrete ByteAuth.concrete value.bv) width)
    (buf : alloc.vec.Vec U8) (hsize : buf.length + 10 ≤ Usize.max) :
    ∃ after, _root_.SpqrReference.encode_varint (UScalar.cast .U64 value) buf = .ok after ∧
      vecContents after = vecContents buf ++ Varint.encode Sha256.concrete ByteAuth.concrete value.bv width := by
  obtain ⟨after, ha, hv⟩ := encode_appends (UScalar.cast .U64 value) buf hsize
  refine ⟨after, ha, ?_⟩
  rw [U32.cast_U64_val_eq] at hv
  exact hv.trans (congrArg (fun bytes => vecContents buf ++ bytes)
    (LibSignalReference.Candidate.ProstEncoding.encode_publicNat value.bv width hw1 hw5 canonical).symm)

/-- The exported guarded uint64 operation prepends its secret success byte
to the actual SPQR bytes on the canonical-width domain. -/
theorem uint64_guarded_refines_artifact (value : U64) (width : Nat) (hw1 : 1 ≤ width) (hw10 : width ≤ 10)
    (canonical : Varint64.canonicalGroups (Varint64.groups Varint64.concrete value.bv) width)
    (buf : alloc.vec.Vec U8) (hsize : buf.length + 10 ≤ Usize.max)
    (secret : _root_.Std.Tactic.BVDecide.BVExpr 64)
    (assign : _root_.Std.Tactic.BVDecide.BVExpr.Assignment)
    (hsecret : secret.eval assign = value.bv) :
    ∃ after, _root_.SpqrReference.encode_varint value buf = .ok after ∧
      ∀ (index : Nat)
        (hi : index < 8 * (Varint64.encodeCore Varint64.symbolic ByteAuth.symbolic secret width).length),
        AigExport.evalRef
          (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
            (Varint64.encodeCore Varint64.symbolic ByteAuth.symbolic secret width))).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
            (Varint64.encodeCore Varint64.symbolic ByteAuth.symbolic secret width))).vec.get index hi)) =
          (ByteCircuit.joinValue (255 :: (vecContents after).drop (vecContents buf).length)).getLsbD index := by
  obtain ⟨after, ha, hv⟩ := encode_uint64 value width hw1 hw10 canonical buf hsize
  have written : (vecContents after).drop (vecContents buf).length =
      Varint64.encode Varint64.concrete ByteAuth.concrete value.bv width := by
    rw [hv]
    simp
  refine ⟨after, ha, ?_⟩
  intro index hi
  rw [Varint64.compiled_encodeCore_correct, hsecret, Varint64.encodeCore_spec, if_pos canonical, written]

end LibSignalReference.Candidate.SpqrVarint
