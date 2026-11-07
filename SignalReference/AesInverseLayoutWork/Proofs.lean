import AesInverseLayoutWork.Generated.WriteReordered.Funs
import AesInverseLayoutWork.Circuit
import LibSignalReference.Proofs.AesLayoutReference

namespace LibSignalReference.Proofs.AesInverseWrite

open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal.AesInverseWrite
open LibSignalReference.Proofs.AesLayout
open _root_.Std.Tactic.BVDecide

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def resultSlice (column : BitVec 64) (initial : Nat → BitVec 8) : Slice U8 :=
  ⟨(value column initial).map (fun byte => ⟨byte⟩), by simp [value]; scalar_tac⟩

theorem shift_right_i32 (x : U64) (s : I32) (hs0 : 0 ≤ s.val) (hs : s.toNat < 64) :
    (x >>> s) = .ok ⟨x.bv >>> s.toNat⟩ := by
  change (if s.val ≥ 0 then (if s.toNat < 64 then _ else _) else _) = _
  simp only [hs0, hs, if_pos]
  rfl

/-- Exact success behavior on the twelve-byte slices used by the enclosing
Rust wrapper. All 160 bits of the column and initial slice are unrestricted.
This statement makes no claim about the unextracted wrapper or other lengths. -/
theorem write_reference (column : U64) (initial : Nat → U8) :
    RustCryptoAesInverseWrite.soft.fixslice.inv_bitslice.write_reordered
      column (slice12 initial) =
      .ok (resultSlice column.bv (fun byte => (initial byte).bv)) := by
  simp [RustCryptoAesInverseWrite.soft.fixslice.inv_bitslice.write_reordered,
    slice12, resultSlice, value, Slice.update, lift, shift_right_i32, UScalar.cast]
  rfl

theorem encode_resultSlice (column : BitVec 64) (initial : Nat → BitVec 8) :
    (resultSlice column initial).val.map UScalar.bv = value column initial := by
  simp [resultSlice, List.map_map, Function.comp_def]

/-- The compiled numeric circuit equals the returned bytes of the actual
translated Rust writer, including the four bytes left untouched by Rust. -/
theorem write_refines_artifact (column : U64) (initial : Nat → U8)
    (secretColumn : BVExpr 64) (secretInitial : Nat → BVExpr 8)
    (assign : BVExpr.Assignment)
    (hcolumn : secretColumn.eval assign = column.bv)
    (hinitial : ∀ byte, (secretInitial byte).eval assign = (initial byte).bv) :
    ∃ result,
      RustCryptoAesInverseWrite.soft.fixslice.inv_bitslice.write_reordered
        column (slice12 initial) = .ok result ∧
      ∀ (index : Nat) (hi : index < 8 * (expr secretColumn secretInitial).length),
        AigExport.evalRef
          (AigExport.exportNodes (AigExport.compile
            (ByteCircuit.joinExpr (expr secretColumn secretInitial))).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (AigExport.exportRef ((AigExport.compile
            (ByteCircuit.joinExpr (expr secretColumn secretInitial))).vec.get index hi)) =
          (ByteCircuit.joinValue (result.val.map UScalar.bv)).getLsbD index := by
  refine ⟨resultSlice column.bv (fun byte => (initial byte).bv),
    write_reference column initial, ?_⟩
  intro index hi
  rw [encode_resultSlice, compiled_expr_correct, hcolumn,
    show (fun byte => (secretInitial byte).eval assign) = (fun byte => (initial byte).bv) from
      funext hinitial]

end LibSignalReference.Proofs.AesInverseWrite
