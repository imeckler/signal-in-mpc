import CtrReferenceV1Work.ParallelCallbackV1Work.Generated.Funs
import CtrReferenceV1Work.CheckedRemainingV1Work.Reference
namespace LibSignalReference.Candidate.ParallelCallback4
open Aeneas Aeneas.Std
open LibSignalReference.Candidate.FixedDispatch
open LibSignalReference.Candidate.FixsliceCircuitV1
open TlsMpc.Signal.AesLayout TlsMpc.Signal.AesLinear
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def backend (keys : Nat → Words (BitVec 64)) (counter : U32) : ActualParallelCallback4.Backend :=
 ⟨counter,(CtrState.zeroNonce counter).nonce,AesKeyRanges.keyArray keys⟩

theorem backend_roundtrip (value : ActualParallelCallback4.Backend) :
 ActualParallelCallback4.fromBackend (ActualParallelCallback4.toBackend value) = value := rfl

theorem owner_roundtrip (value : ActualParallelCallback4.InOut) :
 ActualParallelCallback4.fromInOut (ActualParallelCallback4.toInOut value) = value := rfl

theorem actual_generator (keys : Nat → Words (BitVec 64)) (counter : U32)
 (old : Array (Array U8 16#usize) 4#usize) :
 ActualParallelCallback4.Backend.gen_par_ks_blocks (backend keys counter) old =
 .ok (backend keys (FixedCtr.after 4 counter),
  AesInverseCircuit.originalBatch (encrypted keys (ParallelCtr4.counterInput counter))) := by
 unfold ActualParallelCallback4.Backend.gen_par_ks_blocks
 change (do
  let (next,output) ← ActualParallelCtr4.CtrBackend.gen_par_ks_blocks (ParallelCtr4.backend keys counter) old
  .ok (ActualParallelCallback4.fromBackend next,output)) = _
 rw [ParallelCtr4.generator_actual]
 rfl

theorem actual_xor (input data : Nat → Nat → BitVec 8)
 (old : Array (Array U8 16#usize) 4#usize) :
 ActualParallelCallback4.InOut.xor_in2out
  ⟨AesInverseCircuit.originalBatch input,old⟩ (AesInverseCircuit.originalBatch data) =
 .ok (⟨AesInverseCircuit.originalBatch input,
   AesInverseCircuit.originalBatch (fun r c=>input r c ^^^ data r c)⟩,
  (fun value=>⟨AesInverseCircuit.originalBatch input,value.output⟩)) := by
 unfold ActualParallelCallback4.InOut.xor_in2out
 change (do
  let (updated,back) ← ActualParallelXor4.InOut.xor_in2out
    ⟨ParallelXor4.batch input,old⟩ (ParallelXor4.batch data)
  .ok (ActualParallelCallback4.fromInOut updated,
   fun value=>ActualParallelCallback4.fromInOut (back (ActualParallelCallback4.toInOut value)))) = _
 rw [ParallelXor4.source_xor]
 rfl

theorem actual_chunk (keys : Nat → Words (BitVec 64)) (counter : U32)
 (input : Nat → Nat → BitVec 8) (old : Array (Array U8 16#usize) 4#usize) :
 ActualParallelCallback4.apply_parallel_chunk (backend keys counter)
  ⟨AesInverseCircuit.originalBatch input,old⟩ =
 .ok (backend keys (FixedCtr.after 4 counter),
  ⟨AesInverseCircuit.originalBatch input,AesInverseCircuit.originalBatch
   (fun r c=>input r c ^^^ encrypted keys (ParallelCtr4.counterInput counter) r c)⟩) := by
 simp only [ActualParallelCallback4.apply_parallel_chunk,default_batch,bind_tc_ok]
 rw [actual_generator]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [actual_xor]
 rfl

theorem checked_chunk_no_wrap (counter : U32) (tail : List U8) (ht : tail.length=15)
 (accepted : ActualCheckedCtr16.Wrapper.check_remaining
  (CheckedCtr16.wrapper counter ⟨15,by decide⟩ tail ht) 64#usize = .ok (.Ok ())) :
 (FixedCtr.after 4 counter).val = counter.val+4 := by
 have h := CheckedCtr16.accepted_no_wrap counter ⟨15,by decide⟩ tail ht (64#usize) accepted
 have hc : FixedCtr.requiredBlocks (64#usize).val (15-(⟨15,by decide⟩ : Fin 16).val)=4 := by decide
 rw [hc] at h
 exact FixedCtr.after_no_wrap 4 counter h

end LibSignalReference.Candidate.ParallelCallback4
