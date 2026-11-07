import AesKeyScheduleWork.ColumnsReference

namespace LibSignalReference.Candidate.AesKeyColumns

open Aeneas Aeneas.Std TlsMpc
open _root_.Std.Tactic.BVDecide

theorem update_bv (offset distance rotation index : Nat) (words : Slice U64) :
    (update offset distance rotation index words).val.map UScalar.bv =
      (words.val.map UScalar.bv).set (offset + index)
        (Signal.AesKeyColumns.column Signal.AesKeyColumns.concrete rotation
          ((words.val.map UScalar.bv)[offset + index - distance]?.getD 0#64)
          ((words.val.map UScalar.bv)[offset + index]?.getD 0#64)) := by
  simp only [update, Slice.setAtNat, List.map_set, List.getElem?_map]
  cases words.val[offset + index - distance]? <;> cases words.val[offset + index]? <;> rfl

theorem run_bv (offset distance rotation index count : Nat) (words : Slice U64) :
    (run offset distance rotation index count words).val.map UScalar.bv =
      Signal.AesKeyColumns.run 0 (Signal.AesKeyColumns.column Signal.AesKeyColumns.concrete rotation)
        offset distance index count (words.val.map UScalar.bv) := by
  induction count generalizing index words with
  | zero => rfl
  | succ count ih =>
    simp only [run, Signal.AesKeyColumns.run, ih]
    congr 1
    exact update_bv offset distance rotation index words

/-- All word values and all public in-bounds offsets/distances are covered,
including overlapping ranges. The actual checked loop order is preserved. -/
theorem xor_columns_refines_artifact (offset distance : Usize) (rotation : U32) (words : Slice U64)
    (hd : distance.val ≤ offset.val) (hs : offset.val + 8 ≤ words.length)
    (secretWords : List (BVExpr 64)) (assign : BVExpr.Assignment)
    (hwords : secretWords.map (BVExpr.eval assign) = words.val.map UScalar.bv) :
    ∃ result,
      RustCryptoAesKeySchedule.soft.fixslice.xor_columns words offset distance rotation = .ok result ∧
      ∀ (index : Nat) (hi : index <
          8 * (Signal.AesKeyColumns.expr offset.val distance.val rotation.val secretWords).length),
        AigExport.evalRef
          (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
            (Signal.AesKeyColumns.expr offset.val distance.val rotation.val secretWords))).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
            (Signal.AesKeyColumns.expr offset.val distance.val rotation.val secretWords))).vec.get index hi)) =
          (ByteCircuit.joinValue (Signal.AesKeyCopy.encode (result.val.map UScalar.bv))).getLsbD index := by
  refine ⟨run offset.val distance.val rotation.val 0 8 words,
    xor_columns_spec offset distance rotation words hd hs, ?_⟩
  intro index hi
  rw [Signal.AesKeyColumns.compiled_expr_correct, hwords, run_bv]
  rfl

end LibSignalReference.Candidate.AesKeyColumns
