import AesKeyScheduleLeavesWork.Equalities
import AesKeyScheduleLeavesWork.SubBytes
import LibSignalReference.Proofs.AesShift

namespace LibSignalReference.Proofs.AesKeyScheduleLeaves

open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal.AesLayout TlsMpc.Signal.AesLinear
open LibSignalReference.Proofs.AesLayout LibSignalReference.Proofs.AesLinear
open _root_.Std.Tactic.BVDecide

theorem inverse1_reference (words : Words (BitVec 64)) :
    RustCryptoAesKeySchedule.soft.fixslice.inv_shift_rows_1 (wordSlice words) =
      .ok (wordSlice (mapWords shiftWord3 words)) := by
  rw [inverse1_eq]
  exact shift3_reference words

theorem inverse2_reference (words : Words (BitVec 64)) :
    RustCryptoAesKeySchedule.soft.fixslice.inv_shift_rows_2 (wordSlice words) =
      .ok (wordSlice (mapWords shiftWord2 words)) := by
  rw [inverse2_eq]
  exact shift2_reference words

theorem inverse3_reference (words : Words (BitVec 64)) :
    RustCryptoAesKeySchedule.soft.fixslice.inv_shift_rows_3 (wordSlice words) =
      .ok (wordSlice (mapWords shiftWord1 words)) := by
  rw [inverse3_eq]
  exact shift1_reference words

theorem inverse1_slice (state : Slice U64) (hlen : state.length = 8) :
    ∃ result, RustCryptoAesKeySchedule.soft.fixslice.inv_shift_rows_1 state = .ok result ∧
      result.val.map UScalar.bv =
        (state.val.map UScalar.bv).map TlsMpc.Signal.AesKeySchedule.concrete.inv1 := by
  obtain ⟨words, rfl⟩ := slice_as_wordSlice state hlen
  refine ⟨wordSlice (mapWords shiftWord3 words), inverse1_reference words, ?_⟩
  simp [wordSlice, mapWords, Words.list, TlsMpc.Signal.AesKeySchedule.concrete]

theorem inverse2_slice (state : Slice U64) (hlen : state.length = 8) :
    ∃ result, RustCryptoAesKeySchedule.soft.fixslice.inv_shift_rows_2 state = .ok result ∧
      result.val.map UScalar.bv =
        (state.val.map UScalar.bv).map TlsMpc.Signal.AesKeySchedule.concrete.inv2 := by
  obtain ⟨words, rfl⟩ := slice_as_wordSlice state hlen
  refine ⟨wordSlice (mapWords shiftWord2 words), inverse2_reference words, ?_⟩
  simp [wordSlice, mapWords, Words.list, TlsMpc.Signal.AesKeySchedule.concrete]

theorem inverse3_slice (state : Slice U64) (hlen : state.length = 8) :
    ∃ result, RustCryptoAesKeySchedule.soft.fixslice.inv_shift_rows_3 state = .ok result ∧
      result.val.map UScalar.bv =
        (state.val.map UScalar.bv).map TlsMpc.Signal.AesKeySchedule.concrete.inv3 := by
  obtain ⟨words, rfl⟩ := slice_as_wordSlice state hlen
  refine ⟨wordSlice (mapWords shiftWord1 words), inverse3_reference words, ?_⟩
  simp [wordSlice, mapWords, Words.list, TlsMpc.Signal.AesKeySchedule.concrete]

theorem inverse1_rejects_shape (words : Slice U64) (h : Slice.len words ≠ 8#usize) :
    RustCryptoAesKeySchedule.soft.fixslice.inv_shift_rows_1 words = .fail .assertionFailure := by
  rw [inverse1_eq]
  exact shift3_rejects_shape words h

theorem inverse2_rejects_shape (words : Slice U64) (h : Slice.len words ≠ 8#usize) :
    RustCryptoAesKeySchedule.soft.fixslice.inv_shift_rows_2 words = .fail .assertionFailure := by
  rw [inverse2_eq]
  exact shift2_rejects_shape words h

theorem inverse3_rejects_shape (words : Slice U64) (h : Slice.len words ≠ 8#usize) :
    RustCryptoAesKeySchedule.soft.fixslice.inv_shift_rows_3 words = .fail .assertionFailure := by
  rw [inverse3_eq]
  exact shift1_rejects_shape words h

theorem inverse1_refines_artifact (input : Nat → Nat → BitVec 8)
    (secret : Nat → Nat → BVExpr 8) (assign : BVExpr.Assignment)
    (hsecret : ∀ block index, (secret block index).eval assign = input block index) :
    ∃ result,
      RustCryptoAesKeySchedule.soft.fixslice.inv_shift_rows_1 (wordSlice (network input)) = .ok result ∧
      ∀ (index : Nat) (hi : index < 8 * (shiftNExpr 3 secret).length),
        AigExport.evalRef
          (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (shiftNExpr 3 secret))).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (shiftNExpr 3 secret))).vec.get index hi)) =
          (ByteCircuit.joinValue (encodeResult result)).getLsbD index := by
  rw [inverse1_eq]
  exact shift3_refines_artifact input secret assign hsecret

theorem inverse2_refines_artifact (input : Nat → Nat → BitVec 8)
    (secret : Nat → Nat → BVExpr 8) (assign : BVExpr.Assignment)
    (hsecret : ∀ block index, (secret block index).eval assign = input block index) :
    ∃ result,
      RustCryptoAesKeySchedule.soft.fixslice.inv_shift_rows_2 (wordSlice (network input)) = .ok result ∧
      ∀ (index : Nat) (hi : index < 8 * (shiftNExpr 2 secret).length),
        AigExport.evalRef
          (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (shiftNExpr 2 secret))).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (shiftNExpr 2 secret))).vec.get index hi)) =
          (ByteCircuit.joinValue (encodeResult result)).getLsbD index := by
  rw [inverse2_eq]
  exact shift2_refines_artifact input secret assign hsecret

theorem inverse3_refines_artifact (input : Nat → Nat → BitVec 8)
    (secret : Nat → Nat → BVExpr 8) (assign : BVExpr.Assignment)
    (hsecret : ∀ block index, (secret block index).eval assign = input block index) :
    ∃ result,
      RustCryptoAesKeySchedule.soft.fixslice.inv_shift_rows_3 (wordSlice (network input)) = .ok result ∧
      ∀ (index : Nat) (hi : index < 8 * (shiftExpr secret).length),
        AigExport.evalRef
          (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (shiftExpr secret))).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (shiftExpr secret))).vec.get index hi)) =
          (ByteCircuit.joinValue (encodeResult result)).getLsbD index := by
  rw [inverse3_eq]
  exact shift_refines_artifact input secret assign hsecret

end LibSignalReference.Proofs.AesKeyScheduleLeaves
