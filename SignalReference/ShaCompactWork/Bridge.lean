import ShaCompactWork.Compression

namespace SignalReference.ShaCompact

open Aeneas Aeneas.Std TlsMpc TlsMpc.Sha256
open LibSignalReference.Proofs.Sha256Round
open _root_.Std.Tactic.BVDecide

theorem compress_all_arrays (state : Array U32 8#usize) (block : Array U32 16#usize) :
    CandidateShaStep.sha256.soft.compact.compress_u32 state block =
      .ok (encodeState (Signal.ShaCompact.compress concrete (decodeState state) (value block))) := by
  simpa only [encode_decode] using compress_spec (decodeState state) block

/-- Complete selected-operation refinement: all eight input state words and all
sixteen block words; the actual translated operation succeeds, and every
numeric artifact output bit equals its big-endian state encoding. -/
theorem compress_refines_artifact
    (state : Array U32 8#usize) (block : Array U32 16#usize)
    (secretState : State (BVExpr 32)) (secretBlock : List (BVExpr 32))
    (assign : BVExpr.Assignment)
    (hstate : secretState.map (BVExpr.eval assign) = decodeState state)
    (hblock : secretBlock.map (BVExpr.eval assign) = value block) :
    ∃ result,
      CandidateShaStep.sha256.soft.compact.compress_u32 state block = .ok result ∧
      ∀ (index : Nat) (hi : index < 8 * (Signal.ShaCompact.bytes symbolic secretState secretBlock).length),
        AigExport.evalRef
          (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
            (Signal.ShaCompact.bytes symbolic secretState secretBlock))).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
            (Signal.ShaCompact.bytes symbolic secretState secretBlock))).vec.get index hi)) =
          (ByteCircuit.joinValue (digest concrete (decodeState result))).getLsbD index := by
  refine ⟨encodeState (Signal.ShaCompact.compress concrete (decodeState state) (value block)),
    compress_all_arrays state block, ?_⟩
  intro index hi
  rw [Signal.ShaCompact.compiled_bytes_correct, hstate, hblock, decode_encode]
  rfl

end SignalReference.ShaCompact
