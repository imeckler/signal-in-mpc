import AesCtrBlockWork.FixedDispatchV1Work.GeneratedComplete.Funs
import AesCtrBlockWork.FixsliceCircuitV1Work.Cipher16
namespace LibSignalReference.Candidate.FixedDispatch
open Aeneas Aeneas.Std
open LibSignalReference.Candidate
open LibSignalReference.Candidate.FixsliceCircuitV1
open TlsMpc
open _root_.Std.Tactic.BVDecide
open TlsMpc.Signal.AesLayout TlsMpc.Signal.AesLinear
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

def blockOf (input : Nat → BitVec 8) : Array U8 16#usize :=
 ⟨(List.range 16).map (fun byte => (⟨input byte⟩ : U8)), by simp⟩
def embed (input : Nat → BitVec 8) (block byte : Nat) : BitVec 8 :=
 if block = 0 then input byte else 0

theorem actual_cipher_link : FixedAesDispatch.aes256_encrypt =
 RustCryptoAesCtrBlock.soft.fixslice.aes256_encrypt := rfl

theorem both_writebacks {T : Type} (copy : core.marker.Copy T)
 (input old : T) :
 FixedAesDispatch.InOut.get_out copy ⟨input, old⟩ =
 .ok (old, (fun value => ⟨input, value⟩),
   (fun value => ⟨input, value.output⟩)) := rfl

theorem single_batch (input : Nat → BitVec 8) :
 (do let blocks ← core.default.DefaultArray.default 4#usize
       (core.default.DefaultArray 16#usize core.default.DefaultU8)
     Array.update blocks 0#usize (blockOf input)) =
 .ok (AesInverseCircuit.originalBatch (embed input)) := by
 simp [core.default.DefaultArray.default, core.default.DefaultU8.default,
  Array.repeat, Array.update, blockOf, AesInverseCircuit.originalBatch, embed,
  List.range_succ, UScalar.ofNatCore]
 simp only [UScalar.val]
 rfl

theorem default_batch : core.default.DefaultArray.default 4#usize
 (core.default.DefaultArray 16#usize core.default.DefaultU8) =
 .ok (AesInverseCircuit.originalBatch (fun _ _ => 0)) := by
 simp [core.default.DefaultArray.default, core.default.DefaultU8.default,
  Array.repeat, AesInverseCircuit.originalBatch, List.range_succ, UScalar.ofNatCore]
 simp only [UScalar.val]
 rfl

theorem update_batch (input : Nat → BitVec 8) :
 Array.update (AesInverseCircuit.originalBatch (fun _ _ => 0)) 0#usize (blockOf input) =
 .ok (AesInverseCircuit.originalBatch (embed input)) := by
 simpa only [default_batch, bind_tc_ok] using single_batch input

theorem batch_index_zero (input : Nat → Nat → BitVec 8) :
 Array.index_usize (AesInverseCircuit.originalBatch input) 0#usize =
 .ok (blockOf (input 0)) := by
 simp [Array.index_usize, AesInverseCircuit.originalBatch, blockOf, List.range_succ]

def encrypted (keys : Nat → Words (BitVec 64)) (input : Nat → Nat → BitVec 8) :=
 decode64 (encrypt concrete64 keys (network input))

theorem parallel_actual (keys : Nat → Words (BitVec 64))
 (input : Nat → Nat → BitVec 8) (old : Array (Array U8 16#usize) 4#usize) :
 FixedAesDispatch.Backend.encrypt_par_blocks ⟨AesKeyRanges.keyArray keys⟩
  ⟨AesInverseCircuit.originalBatch input, old⟩ =
 .ok ⟨AesInverseCircuit.originalBatch input,
      AesInverseCircuit.originalBatch (encrypted keys input)⟩ := by
 simp only [FixedAesDispatch.Backend.encrypt_par_blocks, FixedAesDispatch.InOut.get_in,
  FixedAesDispatch.InOut.get_out, bind_tc_ok, actual_cipher_link]
 rw [actual_model]
 rfl

theorem single_actual (keys : Nat → Words (BitVec 64))
 (input : Nat → BitVec 8) (old : Array U8 16#usize) :
 FixedAesDispatch.Backend.encrypt_block ⟨AesKeyRanges.keyArray keys⟩
  ⟨blockOf input, old⟩ =
 .ok ⟨blockOf input, blockOf (encrypted keys (embed input) 0)⟩ := by
 simp only [FixedAesDispatch.Backend.encrypt_block, default_batch,
  FixedAesDispatch.InOut.clone_in, FixedAesDispatch.InOut.get_out,
  core.convert.IntoFrom.into, core.convert.FromSame.from, bind_tc_ok]
 rw [update_batch]
 simp only [bind_tc_ok, actual_cipher_link]
 rw [actual_model]
 simp only [bind_tc_ok, batch_index_zero]
 rfl

theorem selected_original_zero (input : Nat → Nat → BitVec 8) :
 selectedBytes (AesInverseCircuit.originalBatch input) ⟨0, by decide⟩ =
 (blockOf (input 0)).val.map UScalar.bv := by
 simp [selectedBytes, encode_original, blockOf, List.range_succ]

theorem single_computed_compiled (key input : Nat → BVExpr 8)
 (assign : BVExpr.Assignment) (old : Array U8 16#usize) :
 ∃ schedule output,
  RustCryptoAesKeySchedule.soft.fixslice.aes256_key_schedule
   (AesKeySchedule.keyArray (fun i => (⟨(key i).eval assign⟩ : U8))) = .ok schedule ∧
  FixedAesDispatch.Backend.encrypt_block ⟨schedule⟩
   ⟨blockOf (fun i => (input i).eval assign), old⟩ = .ok output ∧
  ∀ (index : Nat) (hi : index < 8 * (singleExpression key input).length),
   AigExport.evalRef
    (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (singleExpression key input))).aig)
    (fun varId bit => (assign.get varId).bv.getLsbD bit)
    (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (singleExpression key input))).vec.get index hi)) =
   (ByteCircuit.joinValue (output.output.val.map UScalar.bv)).getLsbD index := by
 obtain ⟨schedule,hkey,hschedule⟩ := actual_schedule (fun i => (key i).eval assign)
 obtain ⟨schedule2,result,hkey2,hcipher,hbits⟩ :=
  compiled_actual_from_key16 ⟨0, by decide⟩ key (singleInput input) assign
 have heq : schedule2 = schedule := by rw [hkey] at hkey2; exact Result.ok.inj hkey2.symm
 subst schedule2
 rw [hschedule, actual_model] at hcipher
 have hin : (fun b i => (singleInput input b i).eval assign) = embed (fun i => (input i).eval assign) := by
  funext b i
  simp only [singleInput, embed]
  split <;> rfl
 rw [hin] at hcipher
 have hr := Result.ok.inj hcipher
 subst result
 refine ⟨schedule, ⟨blockOf (fun i => (input i).eval assign),
  blockOf (encrypted (groupAt 0 (scheduleValue (fun i => (key i).eval assign)))
   (embed (fun i => (input i).eval assign)) 0)⟩, hkey, ?_, ?_⟩
 · rw [hschedule]
   exact single_actual _ _ _
 · intro index hi
   have hb := hbits index hi
   with_unfolding_all rw [selected_original_zero] at hb
   simpa only [singleExpression, encrypted, hin] using hb

end LibSignalReference.Candidate.FixedDispatch
