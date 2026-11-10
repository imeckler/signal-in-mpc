import CtrReferenceV1Work.ApplyBlockV1Work.Reference
namespace LibSignalReference.Candidate.ApplyBlock16
open Aeneas Aeneas.Std TlsMpc
open _root_.Std.Tactic.BVDecide
open LibSignalReference.Candidate
open LibSignalReference.Candidate.FixedDispatch
open LibSignalReference.Candidate.FixsliceCircuitV1
open TlsMpc.Signal.AesLayout TlsMpc.Signal.AesLinear
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

def expression (key input : Nat → BVExpr 8) (counter : U32) : List (BVExpr 8) :=
 FixedCtr.xorExpression ((List.range 16).map input)
  (FixedCtr.streamExpression (keyGroupsExpression key) counter)

theorem zip_same (xs : List Nat) (a b : Nat → BitVec 8) :
 FixedCtr.xorBytes (xs.map a) (xs.map b) = xs.map (fun i => a i ^^^ b i) := by
 induction xs with
 | nil => rfl
 | cons i xs ih => simp [FixedCtr.xorBytes,ih]

theorem expression_correct (key input : Nat → BVExpr 8) (counter : U32)
 (assign : BVExpr.Assignment) :
 (expression key input counter).map (BVExpr.eval assign) =
 (blockOf (fun i => (input i).eval assign ^^^
  encrypted (groupAt 0 (scheduleValue (fun j => (key j).eval assign)))
   (embed (FixedCtr.blockBytes (CtrState.expected counter))) 0 i)).val.map UScalar.bv := by
 have hk : (fun r => mapWords (BVExpr.eval assign) (keyGroupsExpression key r)) =
  groupAt 0 (scheduleValue (fun j => (key j).eval assign)) := by
  funext r
  exact keyGroupsExpression_correct key assign r
 simp only [expression,FixedCtr.xor_expression_correct,FixedCtr.stream_expression_correct,hk,
  FixedCtr.streamBlock,blockOf,List.map_map,Function.comp_def,UScalar.bv]
 exact zip_same _ _ _

theorem compiled_actual_apply (key input : Nat → BVExpr 8) (counter : U32)
 (assign : BVExpr.Assignment) (old : Array U8 16#usize) :
 ∃ schedule output last,
  RustCryptoAesKeySchedule.soft.fixslice.aes256_key_schedule
   (AesKeySchedule.keyArray (fun i => (⟨(key i).eval assign⟩ : U8))) = .ok schedule ∧
  ActualApplyBlock16.ApplyBlockCtx.call ⟨⟨blockOf (fun i => (input i).eval assign),old⟩⟩
   ⟨counter,(FixedCtr.zeroNonce counter).nonce,schedule⟩ = .ok (output,last) ∧
  last.counter = FixedCtr.successor counter ∧ last.nonce = (FixedCtr.zeroNonce counter).nonce ∧
  last.keys = schedule ∧
  ∀ (index : Nat) (hi : index < 8*(expression key input counter).length),
   AigExport.evalRef
    (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (expression key input counter))).aig)
    (fun varId bit => (assign.get varId).bv.getLsbD bit)
    (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (expression key input counter))).vec.get index hi)) =
   (ByteCircuit.joinValue (output.block.output.val.map UScalar.bv)).getLsbD index := by
 obtain ⟨schedule,hkey,hkeys⟩ := actual_schedule (fun i => (key i).eval assign)
 let keys := groupAt 0 (scheduleValue (fun i => (key i).eval assign))
 refine ⟨schedule,⟨⟨blockOf (fun i => (input i).eval assign),
  blockOf (fun i => (input i).eval assign ^^^
   encrypted keys (embed (FixedCtr.blockBytes (CtrState.expected counter))) 0 i)⟩⟩,
  backend keys (FixedCtr.successor counter),hkey,?_,rfl,rfl,?_,?_⟩
 · rw [hkeys]
   exact actual_apply _ _ _ _
 · exact hkeys.symm
 · intro index hi
   rw [ByteCircuit.compile_bytes_correct,expression_correct]

end LibSignalReference.Candidate.ApplyBlock16
