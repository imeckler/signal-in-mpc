import CtrReferenceV1Work.TailGeneratorV1Work.Generated.Funs
import CtrReferenceV1Work.CheckedRemainingV1Work.Reference
namespace LibSignalReference.Candidate.CtrTail16
open Aeneas Aeneas.Std
open TlsMpc.Signal.AesLayout TlsMpc.Signal.AesLinear
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def backend (keys : Nat → Words (BitVec 64)) (counter : U32) : ActualCtrTail16.Backend :=
 ⟨counter,(FixedCtr.zeroNonce counter).nonce,AesKeyRanges.keyArray keys⟩

theorem actual_generator (keys : Nat → Words (BitVec 64)) (counter : U32)
 (old : Array U8 16#usize) :
 ActualCtrTail16.Backend.gen_ks_block (backend keys counter) old =
 .ok (backend keys (FixedCtr.successor counter),FixedCtr.streamBlock keys counter) := by
 unfold ActualCtrTail16.Backend.gen_ks_block
 change (do
  let (next,block) ← ActualApplyBlock16.Backend.gen_ks_block (ApplyBlock16.backend keys counter) old
  .ok (ActualCtrTail16.fromActual next,block)) = _
 rw [ApplyBlock16.actual_generator]
 rfl

def put (value : core.slice.iter.IterMut (Array U8 16#usize)) (i : Nat)
 (block : Array U8 16#usize) := {value with slice:=value.slice.setAtNat i block}

theorem body_step (keys : Nat → Words (BitVec 64)) (counter : U32)
 (blocks : Slice (Array U8 16#usize)) (i : Nat) (hi : i < blocks.val.length)
 (back : core.slice.iter.IterMut (Array U8 16#usize) → core.slice.iter.IterMut (Array U8 16#usize)) :
 ActualCtrTail16.Backend.gen_tail_blocks_loop.body ⟨blocks,i⟩ back (backend keys counter) =
 .ok (.cont (⟨blocks,i+1⟩,fun value => back (put value i (FixedCtr.streamBlock keys counter)),
  backend keys (FixedCtr.successor counter))) := by
 simp [ActualCtrTail16.Backend.gen_tail_blocks_loop.body,
  core.slice.iter.IteratorIterMut.next,hi,actual_generator,put,uncurry_apply_pair]

theorem body_done (keys : Nat → Words (BitVec 64)) (counter : U32)
 (blocks : Slice (Array U8 16#usize)) (i : Nat) (hi : blocks.val.length ≤ i)
 (back : core.slice.iter.IterMut (Array U8 16#usize) → core.slice.iter.IterMut (Array U8 16#usize)) :
 ActualCtrTail16.Backend.gen_tail_blocks_loop.body ⟨blocks,i⟩ back (backend keys counter) =
 .ok (.done (backend keys counter,back ⟨blocks,i⟩)) := by
 have hn : ¬ i < blocks.val.length := by omega
 simp [ActualCtrTail16.Backend.gen_tail_blocks_loop.body,
  core.slice.iter.IteratorIterMut.next,hn]

def blocks (n : Fin 4) (value : Nat → Array U8 16#usize) : Slice (Array U8 16#usize) :=
 ⟨(List.range n.val).map value,by simp only [List.length_map,List.length_range]; have h:=n.isLt; scalar_tac⟩

theorem tail_unfold (self : ActualCtrTail16.Backend) (value : Slice (Array U8 16#usize))
 (bound : value.val.length < 4) :
 ActualCtrTail16.Backend.gen_tail_blocks self value = (do
  let (next,iter) ← ActualCtrTail16.Backend.gen_tail_blocks_loop ⟨value,0⟩ (fun x=>x) self
  .ok (next,iter.slice)) := by
 have hlt : Slice.len value < 4#usize := by
  change (Slice.len value).val < 4
  rw [Slice.len_val]
  exact bound
 simp only [ActualCtrTail16.Backend.gen_tail_blocks,massert,hlt,↓reduceIte,
  bind_tc_ok,ActualCtrTail16.MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter,
  core.slice.Slice.iter_mut,uncurry_apply_pair]

theorem loop_0 (keys : Nat → Words (BitVec 64)) (counter : U32)
 (old : Nat → Array U8 16#usize) :
 ActualCtrTail16.Backend.gen_tail_blocks_loop ⟨blocks ⟨0,by decide⟩ old,0⟩ (fun x=>x) (backend keys counter) =
 .ok (backend keys (FixedCtr.after 0 counter),
  ⟨blocks ⟨0,by decide⟩ (fun i=>FixedCtr.streamBlock keys (FixedCtr.after i counter)),0⟩) := by
 simp only [ActualCtrTail16.Backend.gen_tail_blocks_loop]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 with_unfolding_all erw [body_done keys (FixedCtr.after 0 counter)
  (blocks ⟨0,by decide⟩ old) 0 (by simp [blocks]) (fun x=>x)]
 simp only [bind_tc_ok,put,blocks,Slice.setAtNat,List.range_succ]
 rfl

theorem loop_1 (keys : Nat → Words (BitVec 64)) (counter : U32)
 (old : Nat → Array U8 16#usize) :
 ActualCtrTail16.Backend.gen_tail_blocks_loop ⟨blocks ⟨1,by decide⟩ old,0⟩ (fun x=>x) (backend keys counter) =
 .ok (backend keys (FixedCtr.after 1 counter),
  ⟨blocks ⟨1,by decide⟩ (fun i=>FixedCtr.streamBlock keys (FixedCtr.after i counter)),1⟩) := by
 simp only [ActualCtrTail16.Backend.gen_tail_blocks_loop]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 with_unfolding_all erw [body_step keys (FixedCtr.after 0 counter)
  (blocks ⟨1,by decide⟩ old) 0 (by simp [blocks]) (fun x=>x)]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 with_unfolding_all erw [body_done keys (FixedCtr.after 1 counter)
  (blocks ⟨1,by decide⟩ old) 1 (by simp [blocks]) (fun value=> (fun x=>x) (put value 0 (FixedCtr.streamBlock keys (FixedCtr.after 0 counter))))]
 simp only [bind_tc_ok,put,blocks,Slice.setAtNat,List.range_succ]
 rfl

theorem loop_2 (keys : Nat → Words (BitVec 64)) (counter : U32)
 (old : Nat → Array U8 16#usize) :
 ActualCtrTail16.Backend.gen_tail_blocks_loop ⟨blocks ⟨2,by decide⟩ old,0⟩ (fun x=>x) (backend keys counter) =
 .ok (backend keys (FixedCtr.after 2 counter),
  ⟨blocks ⟨2,by decide⟩ (fun i=>FixedCtr.streamBlock keys (FixedCtr.after i counter)),2⟩) := by
 simp only [ActualCtrTail16.Backend.gen_tail_blocks_loop]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 with_unfolding_all erw [body_step keys (FixedCtr.after 0 counter)
  (blocks ⟨2,by decide⟩ old) 0 (by simp [blocks]) (fun x=>x)]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 with_unfolding_all erw [body_step keys (FixedCtr.after 1 counter)
  (blocks ⟨2,by decide⟩ old) 1 (by simp [blocks]) (fun value=> (fun x=>x) (put value 0 (FixedCtr.streamBlock keys (FixedCtr.after 0 counter))))]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 with_unfolding_all erw [body_done keys (FixedCtr.after 2 counter)
  (blocks ⟨2,by decide⟩ old) 2 (by simp [blocks]) (fun value=> (fun value=> (fun x=>x) (put value 0 (FixedCtr.streamBlock keys (FixedCtr.after 0 counter)))) (put value 1 (FixedCtr.streamBlock keys (FixedCtr.after 1 counter))))]
 simp only [bind_tc_ok,put,blocks,Slice.setAtNat,List.range_succ]
 rfl

theorem loop_3 (keys : Nat → Words (BitVec 64)) (counter : U32)
 (old : Nat → Array U8 16#usize) :
 ActualCtrTail16.Backend.gen_tail_blocks_loop ⟨blocks ⟨3,by decide⟩ old,0⟩ (fun x=>x) (backend keys counter) =
 .ok (backend keys (FixedCtr.after 3 counter),
  ⟨blocks ⟨3,by decide⟩ (fun i=>FixedCtr.streamBlock keys (FixedCtr.after i counter)),3⟩) := by
 simp only [ActualCtrTail16.Backend.gen_tail_blocks_loop]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 with_unfolding_all erw [body_step keys (FixedCtr.after 0 counter)
  (blocks ⟨3,by decide⟩ old) 0 (by simp [blocks]) (fun x=>x)]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 with_unfolding_all erw [body_step keys (FixedCtr.after 1 counter)
  (blocks ⟨3,by decide⟩ old) 1 (by simp [blocks]) (fun value=> (fun x=>x) (put value 0 (FixedCtr.streamBlock keys (FixedCtr.after 0 counter))))]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 with_unfolding_all erw [body_step keys (FixedCtr.after 2 counter)
  (blocks ⟨3,by decide⟩ old) 2 (by simp [blocks]) (fun value=> (fun value=> (fun x=>x) (put value 0 (FixedCtr.streamBlock keys (FixedCtr.after 0 counter)))) (put value 1 (FixedCtr.streamBlock keys (FixedCtr.after 1 counter))))]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 with_unfolding_all erw [body_done keys (FixedCtr.after 3 counter)
  (blocks ⟨3,by decide⟩ old) 3 (by simp [blocks]) (fun value=> (fun value=> (fun value=> (fun x=>x) (put value 0 (FixedCtr.streamBlock keys (FixedCtr.after 0 counter)))) (put value 1 (FixedCtr.streamBlock keys (FixedCtr.after 1 counter)))) (put value 2 (FixedCtr.streamBlock keys (FixedCtr.after 2 counter))))]
 simp only [bind_tc_ok,put,blocks,Slice.setAtNat,List.range_succ]
 rfl


theorem tail_actual (keys : Nat → Words (BitVec 64)) (counter : U32)
 (n : Fin 4) (old : Nat → Array U8 16#usize) :
 ActualCtrTail16.Backend.gen_tail_blocks (backend keys counter) (blocks n old) =
 .ok (backend keys (FixedCtr.after n.val counter),
  blocks n (fun i=>FixedCtr.streamBlock keys (FixedCtr.after i counter))) := by
 rw [tail_unfold _ _ (by simp only [blocks,List.length_map,List.length_range];exact n.isLt)]
 fin_cases n
 · rw [loop_0];rfl
 · rw [loop_1];rfl
 · rw [loop_2];rfl
 · rw [loop_3];rfl


theorem blocks_represents (value : Slice (Array U8 16#usize)) (n : Fin 4)
 (length : value.val.length=n.val) :
 blocks n (fun i => value.val[i]?.getD default) = value := by
 apply Subtype.ext
 apply List.ext_getElem?
 intro j
 by_cases hj : j < n.val
 · cases h : value.val[j]? with
   | none =>
     have hn := List.getElem?_eq_none_iff.mp h
     omega
   | some item =>
     simp only [blocks,List.getElem?_map,List.getElem?_range,hj,↓reduceDIte,
      Option.map_some,h,Option.getD_some]
 · have hn : value.val[j]? = none := List.getElem?_eq_none (by omega)
   simp [blocks,List.getElem?_map,List.getElem?_range,hj,hn]

theorem tail_actual_arbitrary (keys : Nat → Words (BitVec 64)) (counter : U32)
 (value : Slice (Array U8 16#usize)) (bound : value.val.length < 4) :
 ActualCtrTail16.Backend.gen_tail_blocks (backend keys counter) value =
 .ok (backend keys (FixedCtr.after value.val.length counter),
  blocks ⟨value.val.length,bound⟩ (fun i=>FixedCtr.streamBlock keys (FixedCtr.after i counter))) := by
 have h := tail_actual keys counter ⟨value.val.length,bound⟩
  (fun i=>value.val[i]?.getD default)
 rw [blocks_represents value ⟨value.val.length,bound⟩ rfl] at h
 exact h

theorem tail_counter_no_wrap (counter : U32) (n : Fin 4)
 (authorized : counter.val+n.val ≤ 4294967295) :
 (FixedCtr.after n.val counter).val = counter.val+n.val :=
 FixedCtr.after_no_wrap n.val counter authorized


theorem tail_rejects_oversize (self : ActualCtrTail16.Backend)
 (value : Slice (Array U8 16#usize)) (bound : 4 ≤ value.val.length) :
 ActualCtrTail16.Backend.gen_tail_blocks self value = .fail .assertionFailure := by
 have hlt : ¬ Slice.len value < 4#usize := by
  change ¬ (Slice.len value).val < 4
  rw [Slice.len_val]
  exact Nat.not_lt.mpr bound
 simp [ActualCtrTail16.Backend.gen_tail_blocks,massert,hlt]

theorem checked_tail_no_wrap (counter : U32) (n : Fin 4) (dataLen : Usize)
 (length : dataLen.val=16*n.val) (tail : List U8) (ht : tail.length=15)
 (accepted : ActualCheckedCtr16.Wrapper.check_remaining
  (CheckedCtr16.wrapper counter ⟨15,by decide⟩ tail ht) dataLen = .ok (.Ok ())) :
 (FixedCtr.after n.val counter).val = counter.val+n.val := by
 have h := CheckedCtr16.accepted_no_wrap counter ⟨15,by decide⟩ tail ht dataLen accepted
 have he : FixedCtr.requiredBlocks dataLen.val (15-(⟨15,by decide⟩ : Fin 16).val) = n.val := by
  rw [length]
  unfold FixedCtr.requiredBlocks
  change (16*n.val - (15-15) + 15)/16 = n.val
  omega
 rw [he] at h
 exact FixedCtr.after_no_wrap n.val counter h


theorem written_matches_driver (keys : Nat → Words (BitVec 64)) (counter : U32) (n : Fin 4) :
 (blocks n (fun i=>FixedCtr.streamBlock keys (FixedCtr.after i counter))).val =
 FixedCtr.blocksValue keys n.val counter := by
 fin_cases n <;> rfl

end LibSignalReference.Candidate.CtrTail16
