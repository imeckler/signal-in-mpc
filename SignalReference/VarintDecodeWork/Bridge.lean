import VarintDecodeWork.Reference
import TlsMpc.Signal.VarintDecode.Spqr

namespace LibSignalReference.Candidate.VarintDecode
open Aeneas Aeneas.Std TlsMpc
open TlsMpc.Signal.VarintDecode
open _root_.Std.Tactic.BVDecide

/-- Complete selected prefix operation: every shared output bit agrees with
the actual translated SPQR decoder, with exact success/error and cursor data. -/
theorem decode_refines_artifact (bytes : Slice U8) (secret : List (BVExpr 8))
    (assign : BVExpr.Assignment) (hinput : secret.map (BVExpr.eval assign) = contents bytes) :
    ∃ result cursor,
      _root_.SpqrVarintDecode.decode_varint bytes 0#usize = .ok (result, cursor) ∧
      Matches (Spqr.decode (contents bytes)) result cursor ∧
      ∀ (index : Nat) (hi : index < 8 * (Spqr.decodeCore Spqr.symbolic ByteAuth.symbolic secret).length),
        AigExport.evalRef
          (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
            (Spqr.decodeCore Spqr.symbolic ByteAuth.symbolic secret))).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
            (Spqr.decodeCore Spqr.symbolic ByteAuth.symbolic secret))).vec.get index hi)) =
          (ByteCircuit.joinValue (resultBytes result cursor)).getLsbD index := by
  obtain ⟨result, cursor, hd, hm, hb⟩ := decode_bytes_reference bytes
  refine ⟨result, cursor, hd, hm, ?_⟩
  intro index hi
  rw [Spqr.compiled_decodeCore_correct, hinput, hb]

end LibSignalReference.Candidate.VarintDecode
