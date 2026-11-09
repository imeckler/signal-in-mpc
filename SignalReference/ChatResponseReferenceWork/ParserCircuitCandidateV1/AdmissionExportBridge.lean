import ChatResponseReferenceWork.ParserCircuitCandidateV1.AdmissionProgram
import ChatResponseReferenceWork.ParserCircuitCandidateV1.CompiledMixedFeed
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.ParserCircuitCandidateV1
set_option maxRecDepth 100000

theorem admission_export_same_program (o : Word64.Ops B W) (a : ByteAuth.Ops B) (raw : List B) :
    AdmissionExport.run o a raw = runAdmit o a raw := by
  unfold AdmissionExport.run runAdmit compactAdmitOutput expandAdmitInput AdmissionExport.expand
  rfl

theorem admission_export_same_circuit (raw : List (Std.Tactic.BVDecide.BVExpr 8)) :
    HEq (AigExport.compile (ByteCircuit.joinExpr (AdmissionExport.run Word64.symbolic ByteAuth.symbolic raw)))
      (AigExport.compile (ByteCircuit.joinExpr (runAdmit Word64.symbolic ByteAuth.symbolic raw))) := by
  rw [admission_export_same_program]

#print axioms admission_export_same_program
#print axioms admission_export_same_circuit
end ChatResponseReference.ParserCircuitCandidateV1
