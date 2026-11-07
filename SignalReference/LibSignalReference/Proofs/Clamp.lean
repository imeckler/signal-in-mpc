import LibSignalReference.Generated.Clamp.Funs
import LibSignalReference.Proofs.KeyAccessors
import TlsMpc.Signal.Clamp

namespace LibSignalReference.Proofs

open Aeneas Aeneas.Std

def clampU8 (xs : List Aeneas.Std.U8) : List Aeneas.Std.U8 :=
  TlsMpc.Signal.Clamp.apply (· &&& ·) (· ||| ·) (fun n => ⟨BitVec.ofNat 8 n⟩) xs

theorem clamp_spec (xs : Aeneas.Std.Array Aeneas.Std.U8 32#usize) :
    LibSignalClamp.scalar.clamp_integer xs ⦃ result => result.val = clampU8 xs.val ⦄ := by
  unfold LibSignalClamp.scalar.clamp_integer
  step
  step
  step
  step
  step
  step
  step
  step
  step
  simp_all [clampU8, TlsMpc.Signal.Clamp.apply]
  congr 2
  · exact (UScalar.eq_equiv_bv_eq _ _).mpr i1_post2
  · exact (UScalar.eq_equiv_bv_eq _ _).mpr i5_post2

theorem clampU8_map (xs : List Aeneas.Std.U8) :
    (clampU8 xs).map (fun x => x.bv) =
      TlsMpc.Signal.Clamp.value (xs.map (fun x => x.bv)) := by
  exact TlsMpc.Signal.Clamp.apply_map (fun (x : Aeneas.Std.U8) => x.bv)
    _ _ _ _ _ _ (by intros; rfl) (by intros; rfl) (by intros; rfl) xs

theorem clamp_bytes_refines (xs : Aeneas.Std.Array Aeneas.Std.U8 32#usize) :
    ∃ result, LibSignalClamp.scalar.clamp_integer xs = .ok result ∧
      (bytes result).val = TlsMpc.Signal.Clamp.value (bytes xs).val := by
  obtain ⟨result, hr, hbytes⟩ := WP.spec_imp_exists (clamp_spec xs)
  refine ⟨result, hr, ?_⟩
  change result.val.map (fun x => x.bv) = _
  rw [hbytes]
  exact clampU8_map xs.val

theorem clamp_refines_artifact (xs : Aeneas.Std.Array Aeneas.Std.U8 32#usize)
    (input : List (_root_.Std.Tactic.BVDecide.BVExpr 8))
    (assign : _root_.Std.Tactic.BVDecide.BVExpr.Assignment)
    (hinput : input.map (_root_.Std.Tactic.BVDecide.BVExpr.eval assign) = (bytes xs).val) :
    ∃ result, LibSignalClamp.scalar.clamp_integer xs = .ok result ∧
      ∀ (index : Nat) (hi : index < 8 * (TlsMpc.Signal.Clamp.symbolic input).length),
        TlsMpc.AigExport.evalRef
          (TlsMpc.AigExport.exportNodes (TlsMpc.AigExport.compile
            (TlsMpc.ByteCircuit.joinExpr (TlsMpc.Signal.Clamp.symbolic input))).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (TlsMpc.AigExport.exportRef ((TlsMpc.AigExport.compile
            (TlsMpc.ByteCircuit.joinExpr (TlsMpc.Signal.Clamp.symbolic input))).vec.get index hi)) =
        (TlsMpc.ByteCircuit.joinValue (bytes result).val).getLsbD index := by
  obtain ⟨result, hr, hbytes⟩ := clamp_bytes_refines xs
  refine ⟨result, hr, ?_⟩
  intro index hi
  rw [TlsMpc.Signal.Clamp.compiled_clamp_correct, hinput, ← hbytes]

end LibSignalReference.Proofs
