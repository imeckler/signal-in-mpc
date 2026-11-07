import AesAddRoundKeyWork.Circuit
import AesAddRoundKeyWork.Generated.XorAssign.Funs

namespace LibSignalReference.Proofs.AesXorAssign

open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal.AesXorAssign
open _root_.Std.Tactic.BVDecide

/-- This is the actual value-taking core helper called by the shared-argument
forwarder in AES add_round_key. The mutable iterator loop is not included. -/
theorem xor_reference (state key : U64) :
    RustCryptoAesXorAssign.U64.Insts.CoreOpsBitBitXorAssignU64.bitxor_assign state key =
      .ok ⟨state.bv ^^^ key.bv⟩ := by
  rfl

theorem xor_refines_artifact (state key : U64) (secretState secretKey : BVExpr 64)
    (assign : BVExpr.Assignment)
    (hstate : secretState.eval assign = state.bv)
    (hkey : secretKey.eval assign = key.bv) :
    ∃ result,
      RustCryptoAesXorAssign.U64.Insts.CoreOpsBitBitXorAssignU64.bitxor_assign state key = .ok result ∧
      ∀ (index : Nat) (hi : index < 64),
        AigExport.evalRef (AigExport.exportNodes
          (AigExport.compile (expr secretState secretKey)).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (AigExport.exportRef
            ((AigExport.compile (expr secretState secretKey)).vec.get index hi)) =
          result.bv.getLsbD index := by
  refine ⟨⟨state.bv ^^^ key.bv⟩, xor_reference state key, ?_⟩
  intro index hi
  rw [compiled_expr_correct, hstate, hkey]

end LibSignalReference.Proofs.AesXorAssign
