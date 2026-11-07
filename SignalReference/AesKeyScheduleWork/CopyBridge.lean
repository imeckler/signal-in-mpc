import AesKeyScheduleWork.CopyReference
import TlsMpc.Signal.AesKeyCopy

namespace LibSignalReference.Candidate.AesKeyCopy

open Aeneas Aeneas.Std TlsMpc
open _root_.Std.Tactic.BVDecide

theorem copyBackward_val (src dst n : Nat) (words : Slice U64) :
    (copyBackward src dst n words).val =
      Signal.AesKeyCopy.copyBackward 0#u64 src dst n words.val := by
  induction n generalizing words with
  | zero => rfl
  | succ n ih =>
    simp only [copyBackward, Signal.AesKeyCopy.copyBackward, ih]
    rfl

theorem copyBackward_bv (src dst n : Nat) (words : Slice U64) :
    (copyBackward src dst n words).val.map UScalar.bv =
      Signal.AesKeyCopy.copyBackward 0#64 src dst n (words.val.map UScalar.bv) := by
  rw [copyBackward_val, Signal.AesKeyCopy.copyBackward_map]
  rfl

/-- Numeric circuit equality for the actual aligned eight-word copy used by
the key schedule. Indices/shape are public; every word value is unrestricted. -/
theorem memshift32_refines_artifact (src : Usize) (words : Slice U64)
    (halign : src.val % 8 = 0) (hsize : src.val + 16 ≤ words.length)
    (secretWords : List (BVExpr 64)) (assign : BVExpr.Assignment)
    (hwords : secretWords.map (BVExpr.eval assign) = words.val.map UScalar.bv) :
    ∃ result,
      RustCryptoAesKeySchedule.soft.fixslice.memshift32 words src = .ok result ∧
      ∀ (index : Nat) (hi : index < 8 * (Signal.AesKeyCopy.expr src.val secretWords).length),
        AigExport.evalRef
          (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
            (Signal.AesKeyCopy.expr src.val secretWords))).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
            (Signal.AesKeyCopy.expr src.val secretWords))).vec.get index hi)) =
          (ByteCircuit.joinValue (Signal.AesKeyCopy.encode (result.val.map UScalar.bv))).getLsbD index := by
  refine ⟨copyBackward src.val (src.val + 8) 8 words, memshift32_spec src words halign hsize, ?_⟩
  intro index hi
  rw [Signal.AesKeyCopy.compiled_expr_correct, hwords, copyBackward_bv]
  rfl

end LibSignalReference.Candidate.AesKeyCopy
