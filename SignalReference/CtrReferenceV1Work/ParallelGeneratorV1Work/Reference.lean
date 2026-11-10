import CtrReferenceV1Work.ParallelGeneratorV1Work.GeneratedValue.Funs
import CtrReferenceV1Work.FixedGeneratorV1Work.DriverReference
namespace LibSignalReference.Candidate.ParallelCtr4
open Aeneas Aeneas.Std
open LibSignalReference.Candidate
open LibSignalReference.Candidate.FixedDispatch
open LibSignalReference.Candidate.FixsliceCircuitV1
open TlsMpc.Signal.AesLayout TlsMpc.Signal.AesLinear
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def zeroNonce (counter : U32) : ActualParallelCtr4.Nonce :=
 ⟨counter,(CtrState.zeroNonce counter).nonce⟩
def backend (keys : Nat → Words (BitVec 64)) (counter : U32) : ActualParallelCtr4.CtrBackend :=
 ⟨zeroNonce counter,⟨AesKeyRanges.keyArray keys⟩⟩
def zeroBatch : Array (Array U8 16#usize) 4#usize :=
 AesInverseCircuit.originalBatch (fun _ _ => 0)
def iterator (n : Nat) : core.slice.iter.IterMut (Array U8 16#usize) :=
 ⟨zeroBatch.to_slice,n⟩
def put (value : core.slice.iter.IterMut (Array U8 16#usize)) (n : Nat)
 (block : Array U8 16#usize) : core.slice.iter.IterMut (Array U8 16#usize) :=
 {value with slice:=value.slice.setAtNat n block}

theorem actual_next (counter : U32) : ActualParallelCtr4.next_block (zeroNonce counter) =
 .ok (CtrState.expected counter,zeroNonce (FixedCtr.successor counter)) := by
 simp only [ActualParallelCtr4.next_block,ActualParallelCtr4.toActual,zeroNonce]
 change (do
  let (block,next) ← CtrStateV1.next (CtrState.zeroNonce counter)
  .ok (block,ActualParallelCtr4.fromActual next)) = _
 rw [CtrState.actual_next_zero_nonce]
 rfl

theorem parallel_AES (keys : Nat → Words (BitVec 64)) (input : Nat → Nat → BitVec 8)
 (old : Array (Array U8 16#usize) 4#usize) :
 ActualParallelCtr4.Backend.encrypt_par_blocks ⟨AesKeyRanges.keyArray keys⟩
  ⟨AesInverseCircuit.originalBatch input,old⟩ =
 .ok ⟨AesInverseCircuit.originalBatch input,AesInverseCircuit.originalBatch (encrypted keys input)⟩ := by
 simp only [ActualParallelCtr4.Backend.encrypt_par_blocks,ActualParallelCtr4.InOut.get_in,
  ActualParallelCtr4.InOut.get_out,bind_tc_ok,ActualParallelCtr4.aes256_encrypt]
 rw [actual_model]
 rfl

theorem body_step (keys : Nat → Words (BitVec 64)) (counter : U32) (i : Fin 4)
 (back : core.slice.iter.IterMut (Array U8 16#usize) → core.slice.iter.IterMut (Array U8 16#usize)) :
 ActualParallelCtr4.CtrBackend.gen_par_ks_blocks_loop.body (iterator i.val) back (backend keys counter) =
 .ok (.cont (iterator (i.val+1),
  (fun value => back (put value i.val (CtrState.expected counter))),
  backend keys (FixedCtr.successor counter))) := by
 simp [ActualParallelCtr4.CtrBackend.gen_par_ks_blocks_loop.body,
  core.slice.iter.IteratorIterMut.next,iterator,zeroBatch,Array.to_slice,Slice.length,Slice.len,
  AesInverseCircuit.originalBatch,backend,actual_next,put,i.isLt,uncurry_apply_pair]

theorem body_done (keys : Nat → Words (BitVec 64)) (counter : U32)
 (back : core.slice.iter.IterMut (Array U8 16#usize) → core.slice.iter.IterMut (Array U8 16#usize)) :
 ActualParallelCtr4.CtrBackend.gen_par_ks_blocks_loop.body (iterator 4) back (backend keys counter) =
 .ok (.done (backend keys counter,back (iterator 4))) := by
 simp [ActualParallelCtr4.CtrBackend.gen_par_ks_blocks_loop.body,
  core.slice.iter.IteratorIterMut.next,iterator,zeroBatch,Array.to_slice,Slice.length,Slice.len,
  AesInverseCircuit.originalBatch,backend]

def restored (counter : U32) : core.slice.iter.IterMut (Array U8 16#usize) :=
 put (put (put (put (iterator 4) 3 (CtrState.expected (FixedCtr.after 3 counter)))
   2 (CtrState.expected (FixedCtr.after 2 counter)))
   1 (CtrState.expected (FixedCtr.after 1 counter))) 0 (CtrState.expected counter)

theorem loop_four (keys : Nat → Words (BitVec 64)) (counter : U32) :
 ActualParallelCtr4.CtrBackend.gen_par_ks_blocks_loop (iterator 0) (fun value=>value)
  (backend keys counter) = .ok (backend keys (FixedCtr.after 4 counter),restored counter) := by
 simp only [ActualParallelCtr4.CtrBackend.gen_par_ks_blocks_loop]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 with_unfolding_all erw [body_step keys counter ⟨0,by decide⟩ (fun value => value)]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 with_unfolding_all erw [body_step keys (FixedCtr.after 1 counter) ⟨1,by decide⟩ (fun value => (fun value => value) (put value 0 (CtrState.expected counter)))]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 with_unfolding_all erw [body_step keys (FixedCtr.after 2 counter) ⟨2,by decide⟩ (fun value => (fun value => (fun value => value) (put value 0 (CtrState.expected counter))) (put value 1 (CtrState.expected (FixedCtr.after 1 counter))))]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 with_unfolding_all erw [body_step keys (FixedCtr.after 3 counter) ⟨3,by decide⟩ (fun value => (fun value => (fun value => (fun value => value) (put value 0 (CtrState.expected counter))) (put value 1 (CtrState.expected (FixedCtr.after 1 counter)))) (put value 2 (CtrState.expected (FixedCtr.after 2 counter))))]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 with_unfolding_all erw [body_done keys (FixedCtr.after 4 counter) (fun value => (fun value => (fun value => (fun value => (fun value => value) (put value 0 (CtrState.expected counter))) (put value 1 (CtrState.expected (FixedCtr.after 1 counter)))) (put value 2 (CtrState.expected (FixedCtr.after 2 counter)))) (put value 3 (CtrState.expected (FixedCtr.after 3 counter))))]
 simp only [bind_tc_ok]
 rfl

def counterInput (counter : U32) (block byte : Nat) : BitVec 8 :=
 FixedCtr.blockBytes (CtrState.expected (FixedCtr.after block counter)) byte

theorem restored_array (counter : U32) :
 Array.from_slice zeroBatch (restored counter).slice =
 AesInverseCircuit.originalBatch (counterInput counter) := by
 simp only [restored,put,iterator,zeroBatch,Array.from_slice,Array.to_slice,
  Slice.setAtNat,AesInverseCircuit.originalBatch,counterInput,List.range_succ]
 change _ = (⟨[blockOf (FixedCtr.blockBytes (CtrState.expected counter)),
  blockOf (FixedCtr.blockBytes (CtrState.expected (FixedCtr.after 1 counter))),
  blockOf (FixedCtr.blockBytes (CtrState.expected (FixedCtr.after 2 counter))),
  blockOf (FixedCtr.blockBytes (CtrState.expected (FixedCtr.after 3 counter)))],by simp⟩ : Array (Array U8 16#usize) 4#usize)
 simp only [FixedCtr.block_bytes_roundtrip]
 rfl

theorem generator_actual (keys : Nat → Words (BitVec 64)) (counter : U32)
 (old : Array (Array U8 16#usize) 4#usize) :
 ActualParallelCtr4.CtrBackend.gen_par_ks_blocks (backend keys counter) old =
 .ok (backend keys (FixedCtr.after 4 counter),
  AesInverseCircuit.originalBatch (encrypted keys (counterInput counter))) := by
 simp only [ActualParallelCtr4.CtrBackend.gen_par_ks_blocks,FixedDispatch.default_batch,
  bind_tc_ok,uncurry_apply_pair]
 change (do
  let (next, value) ← ActualParallelCtr4.CtrBackend.gen_par_ks_blocks_loop
    (iterator 0) (fun value => value) (backend keys counter)
  let (io, back) ← ActualParallelCtr4.make_inout (Array.from_slice zeroBatch value.slice,old)
  let result ← ActualParallelCtr4.Backend.encrypt_par_blocks next.backend io
  .ok (next,back {io with output:=result.output})) = _
 rw [loop_four]
 simp only [bind_tc_ok,uncurry_apply_pair,restored_array,ActualParallelCtr4.make_inout]
 simp only [bind_tc_ok,uncurry_apply_pair,backend]
 rw [parallel_AES]
 rfl

end LibSignalReference.Candidate.ParallelCtr4
