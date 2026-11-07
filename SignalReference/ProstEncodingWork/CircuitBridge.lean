import ProstEncodingWork.VecBridge

namespace LibSignalReference.Candidate.ProstEncoding

open Aeneas Aeneas.Std
open TlsMpc
open TlsMpc.Signal

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem group_value (word : BitVec 32) (index : Nat) (hi : index < 5) :
    OpenResult.get ByteAuth.concrete (Varint.groups Sha256.concrete ByteAuth.concrete word) index =
      BitVec.ofNat 8 (word.toNat / 128 ^ index % 128) := by
  simp only [Varint.groups, OpenResult.get, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some, Sha256.concrete, ByteAuth.concrete]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  have hm (n : Nat) : n &&& 127 = n % 128 := by
    simpa using Nat.and_two_pow_sub_one_eq_mod n 7
  simp only [hm]
  have hp : 2 ^ (7 * index) = 128 ^ index := by rw [Nat.pow_mul]
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reduceSub, Nat.reducePow] at *
  rw [hp]
  omega

theorem groups_values (word : BitVec 32) :
    Varint.groups Sha256.concrete ByteAuth.concrete word =
      (List.range 5).map (fun index => BitVec.ofNat 8 (word.toNat / 128 ^ index % 128)) := by
  unfold Varint.groups
  apply List.map_congr_left
  intro index hi
  have hb := List.mem_range.mp hi
  simpa only [Varint.groups, OpenResult.get, List.getElem?_map, List.getElem?_range hb,
    Option.map_some, Option.getD_some] using group_value word index hb

theorem groups_naturals (word : BitVec 32) :
    (Varint.groups Sha256.concrete ByteAuth.concrete word).map BitVec.toNat =
      (List.range 5).map (fun index => word.toNat / 128 ^ index % 128) := by
  rw [groups_values, List.map_map]
  apply List.map_congr_left
  intro index hi
  simp only [Function.comp_def, BitVec.toNat_ofNat]
  omega

theorem canonical_width_bounds (word : BitVec 32) (width : Nat)
    (hw1 : 1 ≤ width) (hw5 : width ≤ 5)
    (canonical : Varint.canonicalGroups (Varint.groups Sha256.concrete ByteAuth.concrete word) width) :
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
  have hword : word.toNat < 4294967296 := word.isLt
  have hw : width = 1 ∨ width = 2 ∨ width = 3 ∨ width = 4 ∨ width = 5 := by omega
  rcases hw with rfl | rfl | rfl | rfl | rfl <;>
    simp [List.range_succ] at hz ht ⊢ <;> omega

set_option maxRecDepth 100000 in
private theorem byte_xor_continuation_all : ∀ n : Fin 128,
    BitVec.ofNat 8 n.val ^^^ 128#8 = BitVec.ofNat 8 (n.val + 128) := by
  decide +kernel

theorem byte_xor_continuation (n : Nat) (hn : n < 128) :
    BitVec.ofNat 8 n ^^^ 128#8 = BitVec.ofNat 8 (n + 128) :=
  byte_xor_continuation_all ⟨n, hn⟩

def fixedBytes (value width : Nat) : List (BitVec 8) :=
  (List.range width).map (fun index =>
    BitVec.ofNat 8 (value / 128 ^ index % 128 + if index + 1 < width then 128 else 0))

theorem encode_fixed (word : BitVec 32) (width : Nat) (hw : width ≤ 5) :
    Varint.encode Sha256.concrete ByteAuth.concrete word width = fixedBytes word.toNat width := by
  unfold Varint.encode Varint.encodeGroups fixedBytes
  apply List.map_congr_left
  intro index hi
  have hb := List.mem_range.mp hi
  rw [group_value word index (by omega)]
  by_cases hc : index + 1 < width
  · simpa only [if_pos hc, ByteAuth.concrete] using
      byte_xor_continuation (word.toNat / 128 ^ index % 128) (by omega)
  · simp only [if_neg hc, ByteAuth.concrete, BitVec.xor_zero, Nat.add_zero]

theorem fixedBytes_succ (value width : Nat) :
    fixedBytes value (width + 1) =
      BitVec.ofNat 8 (value % 128 + if 0 < width then 128 else 0) :: fixedBytes (value / 128) width := by
  simp only [fixedBytes, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · simp
  · apply List.map_congr_left
    intro index hi
    simp [Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]

theorem publicNatLoop_fixed (fuel width value : Nat) (hw1 : 1 ≤ width) (hf : width ≤ fuel)
    (upper : value < 128 ^ width) (lower : width = 1 ∨ 128 ^ (width - 1) ≤ value) :
    Varint.publicNatLoop ByteAuth.concrete fuel value = fixedBytes value width := by
  induction width generalizing fuel value with
  | zero => omega
  | succ width ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      cases width with
      | zero =>
        have hv : value < 128 := by simpa using upper
        simp [Varint.publicNatLoop, hv, fixedBytes, Nat.mod_eq_of_lt hv, ByteAuth.concrete]
      | succ width =>
        have hp : 1 ≤ 128 ^ width := Nat.one_le_pow width 128 (by decide)
        have hlarge : 128 ≤ value := by
          simp only [Nat.add_sub_cancel] at lower
          have hl : 128 ^ (width + 1) ≤ value := by omega
          rw [Nat.pow_succ] at hl
          omega
        have hu' : value / 128 < 128 ^ (width + 1) := by
          rw [Nat.pow_succ] at upper
          omega
        have hl' : width + 1 = 1 ∨ 128 ^ (width + 1 - 1) ≤ value / 128 := by
          by_cases hz : width = 0
          · simp [hz]
          · right
            have hl : 128 ^ (width + 1) ≤ value := by
              simp only [Nat.add_sub_cancel] at lower
              omega
            rw [Nat.pow_succ] at hl
            simp only [Nat.add_sub_cancel]
            omega
        rw [Varint.publicNatLoop, if_neg (by omega), fixedBytes_succ]
        simp only [show 0 < width + 1 by omega, if_true]
        exact congrArg (fun rest => BitVec.ofNat 8 (value % 128 + 128) :: rest)
          (ih fuel (value / 128) (by omega) (by omega) hu' hl')

theorem encode_publicNat (word : BitVec 32) (width : Nat) (hw1 : 1 ≤ width) (hw5 : width ≤ 5)
    (canonical : Varint.canonicalGroups (Varint.groups Sha256.concrete ByteAuth.concrete word) width) :
    Varint.encode Sha256.concrete ByteAuth.concrete word width =
      Varint.publicNat ByteAuth.concrete word.toNat := by
  obtain ⟨upper, lower⟩ := canonical_width_bounds word width hw1 hw5 canonical
  rw [encode_fixed word width hw5, Varint.publicNat]
  exact (publicNatLoop_fixed 10 width word.toNat hw1 (by omega) upper lower).symm

theorem accepts_canonical (word : BitVec 32) (width : Nat)
    (accepted : Varint.accepts Sha256.concrete ByteAuth.concrete word width = 255#8) :
    Varint.canonicalGroups (Varint.groups Sha256.concrete ByteAuth.concrete word) width := by
  unfold Varint.accepts at accepted
  rw [Varint.widthMask_value] at accepted
  split at accepted
  · assumption
  · contradiction

/-- The selected actual Rust encoder appends exactly the bytes emitted by the
shared uint32 circuit whenever its public width passes the secret guard. -/
theorem vec_encode_uint32 (value : U32) (width : Nat) (hw1 : 1 ≤ width) (hw5 : width ≤ 5)
    (canonical : Varint.canonicalGroups
      (Varint.groups Sha256.concrete ByteAuth.concrete value.bv) width)
    (buf : Aeneas.Std.alloc.vec.Vec U8) (hsize : buf.length + 10 ≤ Usize.max) :
    ∃ after, _root_.ProstEncoding.encoding.varint.encode_varint vecDictionary
        (UScalar.cast .U64 value) buf = .ok after ∧
      vecContents after = vecContents buf ++ Varint.encode Sha256.concrete ByteAuth.concrete value.bv width := by
  obtain ⟨after, ha, hv⟩ := vec_encode_appends (UScalar.cast .U64 value) buf hsize
  refine ⟨after, ha, ?_⟩
  rw [U32.cast_U64_val_eq] at hv
  exact hv.trans (congrArg (fun bytes => vecContents buf ++ bytes)
    (encode_publicNat value.bv width hw1 hw5 canonical).symm)

/-- Every numeric MPC output bit equals the actual bytes appended by the
faithfully translated generic prost loop with the actual selected Vec methods. -/
theorem uint32_refines_artifact (value : U32) (width : Nat) (hw1 : 1 ≤ width) (hw5 : width ≤ 5)
    (canonical : Varint.canonicalGroups
      (Varint.groups Sha256.concrete ByteAuth.concrete value.bv) width)
    (buf : Aeneas.Std.alloc.vec.Vec U8) (hsize : buf.length + 10 ≤ Usize.max)
    (secret : _root_.Std.Tactic.BVDecide.BVExpr 32)
    (assign : _root_.Std.Tactic.BVDecide.BVExpr.Assignment)
    (hsecret : secret.eval assign = value.bv) :
    ∃ after, _root_.ProstEncoding.encoding.varint.encode_varint vecDictionary
        (UScalar.cast .U64 value) buf = .ok after ∧
      ∀ (index : Nat)
        (hi : index < 8 * (Varint.encode Sha256.symbolic ByteAuth.symbolic secret width).length),
        AigExport.evalRef
          (AigExport.exportNodes (AigExport.compile
            (ByteCircuit.joinExpr (Varint.encode Sha256.symbolic ByteAuth.symbolic secret width))).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (AigExport.exportRef ((AigExport.compile
            (ByteCircuit.joinExpr (Varint.encode Sha256.symbolic ByteAuth.symbolic secret width))).vec.get index hi)) =
          (ByteCircuit.joinValue ((vecContents after).drop (vecContents buf).length)).getLsbD index := by
  obtain ⟨after, ha, hv⟩ := vec_encode_uint32 value width hw1 hw5 canonical buf hsize
  have written : (vecContents after).drop (vecContents buf).length =
      Varint.encode Sha256.concrete ByteAuth.concrete value.bv width := by
    rw [hv]
    simp
  refine ⟨after, ha, ?_⟩
  intro index hi
  rw [Varint.compiled_encode_correct, hsecret]
  exact congrArg (fun bytes => (ByteCircuit.joinValue bytes).getLsbD index) written.symm

end LibSignalReference.Candidate.ProstEncoding
