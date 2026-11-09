import AesCtrBlockWork.FixsliceCircuitV1Work.KeySchedule
namespace LibSignalReference.Candidate.FixsliceCircuitV1
open TlsMpc TlsMpc.Signal.AesLayout TlsMpc.Signal.AesLinear
open Aeneas Aeneas.Std
open _root_.Std.Tactic.BVDecide
attribute [local irreducible] scheduleValue scheduleExpression

def computedExpression64 (key : Nat→BVExpr 8) (input : Nat→Nat→BVExpr 8) : List (BVExpr 8) :=
 expression64 (keyGroupsExpression key) input

/-- Both actual computational components are present: the translated key
schedule result is the exact schedule consumed by the translated AES entry.
No expanded-key input or supplied crypto correctness flag is needed. -/
theorem compiled_actual_from_key64 (key : Nat→BVExpr 8) (input : Nat→Nat→BVExpr 8)
 (assign : BVExpr.Assignment) :
 ∃ schedule result,
  RustCryptoAesKeySchedule.soft.fixslice.aes256_key_schedule
   (AesKeySchedule.keyArray (fun i=>(⟨(key i).eval assign⟩ : U8))) = .ok schedule ∧
  RustCryptoAesCtrBlock.soft.fixslice.aes256_encrypt schedule
   (AesInverseCircuit.originalBatch (fun b i=>(input b i).eval assign)) = .ok result ∧
  ∀ (index : Nat) (hi : index<8*(computedExpression64 key input).length),
   AigExport.evalRef
    (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (computedExpression64 key input))).aig)
    (fun varId bit=>(assign.get varId).bv.getLsbD bit)
    (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (computedExpression64 key input))).vec.get index hi)) =
   (ByteCircuit.joinValue (encodeBatch result)).getLsbD index := by
 obtain ⟨schedule,hkey,hschedule⟩:=actual_schedule (fun i=>(key i).eval assign)
 obtain ⟨result,hcipher,hbits⟩:=compiled_actual64 (keyGroupsExpression key) input assign
 have hgroups : (fun r=>mapWords (BVExpr.eval assign) (keyGroupsExpression key r))=
  groupAt 0 (scheduleValue (fun i=>(key i).eval assign)) := by
  funext r
  exact keyGroupsExpression_correct key assign r
 rw [hgroups,←hschedule] at hcipher
 refine ⟨schedule,result,hkey,hcipher,?_⟩
 simpa only [computedExpression64] using hbits
end LibSignalReference.Candidate.FixsliceCircuitV1
