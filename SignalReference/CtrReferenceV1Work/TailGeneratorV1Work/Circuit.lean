import CtrReferenceV1Work.TailGeneratorV1Work.Reference
namespace LibSignalReference.Candidate.CtrTail16
open Aeneas Aeneas.Std TlsMpc
open _root_.Std.Tactic.BVDecide
open LibSignalReference.Candidate.FixsliceCircuitV1
open TlsMpc.Signal.AesLayout TlsMpc.Signal.AesLinear
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

-- The ciphertext capacity's keystream is an actual key-schedule/tail-generator
-- trace. This does not claim the generic caller's partial-byte/head callbacks.
theorem compiled_fresh_tail (key : Nat → BVExpr 8) (input : List (BVExpr 8))
 (assign : BVExpr.Assignment) (n : Fin 4)
 (count : (input.length+15)/16=n.val) (old : Nat → Array U8 16#usize) :
 ∃ schedule generated,
  RustCryptoAesKeySchedule.soft.fixslice.aes256_key_schedule
   (AesKeySchedule.keyArray (fun i => (⟨(key i).eval assign⟩ : U8))) = .ok schedule ∧
  ActualCtrTail16.Backend.gen_tail_blocks
   ⟨0#u32,(FixedCtr.zeroNonce (0#u32)).nonce,schedule⟩ (blocks n old) =
   .ok (backend (groupAt 0 (scheduleValue (fun i => (key i).eval assign)))
    (FixedCtr.after n.val (0#u32)),generated) ∧
  ∀ (index : Nat) (hi : index < 8*(FixedCtr.freshExpression key input).length),
   AigExport.evalRef
    (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (FixedCtr.freshExpression key input))).aig)
    (fun varId bit => (assign.get varId).bv.getLsbD bit)
    (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (FixedCtr.freshExpression key input))).vec.get index hi)) =
   (ByteCircuit.joinValue (FixedCtr.xorBytes (input.map (BVExpr.eval assign))
    (FixedCtr.bytesOfBlocks generated.val))).getLsbD index := by
 obtain ⟨schedule,hkey,hkeys⟩ := actual_schedule (fun i => (key i).eval assign)
 let keys := groupAt 0 (scheduleValue (fun i => (key i).eval assign))
 refine ⟨schedule,blocks n (fun i=>FixedCtr.streamBlock keys (FixedCtr.after i (0#u32))),hkey,?_,?_⟩
 · rw [hkeys]
   exact tail_actual keys (0#u32) n old
 · intro index hi
   rw [ByteCircuit.compile_bytes_correct,FixedCtr.fresh_expression_correct,
    written_matches_driver,count]
end LibSignalReference.Candidate.CtrTail16
