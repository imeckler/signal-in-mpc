import CtrReferenceV1Work.ParallelXorV1Work.GeneratedSelected.Funs
import CtrReferenceV1Work.XorContentV1Work.LoopReference
import CtrReferenceV1Work.ParallelGeneratorV1Work.Reference
namespace LibSignalReference.Candidate.ParallelXor4
open Aeneas Aeneas.Std
open LibSignalReference.Candidate.FixedDispatch
open LibSignalReference.Candidate.XorContent16
open TlsMpc.Signal.AesLayout
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def batch (f : Nat → Nat → BitVec 8) := AesInverseCircuit.originalBatch f

theorem batch_index (f : Nat → Nat → BitVec 8) (i : Fin 4) :
 Array.index_usize (batch f) (index i.val) = .ok (blockOf (f i.val)) := by
 have hi := index_val i.val (by omega)
 simp [Array.index_usize,batch,AesInverseCircuit.originalBatch,hi,i.isLt,blockOf]

theorem inner_step (input data temp : Nat → Nat → BitVec 8)
 (old : Array (Array U8 16#usize) 4#usize) (i : Fin 4) (j : Fin 16) :
 ActualParallelXor4.InOut.xor_in2out_loop0_loop0.body ⟨batch input,old⟩ (batch data)
  (index i.val) {start:=index j.val,«end»:=16#usize} (batch temp) =
 .ok (.cont ({start:=index (j.val+1),«end»:=16#usize},
  (batch temp).set (index i.val)
   ((blockOf (temp i.val)).set (index j.val) ⟨input i.val j.val ^^^ data i.val j.val⟩))) := by
 simp only [ActualParallelXor4.InOut.xor_in2out_loop0_loop0.body,range_step,
  uncurry_apply_pair,bind_tc_ok,batch_index,block_index,Array.index_mut_usize,
  byte_xor,lift,update_valid]

def rowSet (f : Nat → Nat → BitVec 8) (i : Nat) (row : Nat → BitVec 8) :=
 fun r c => if r = i then row c else f r c

theorem batch_set (f : Nat → Nat → BitVec 8) (i : Fin 4) (row : Nat → BitVec 8) :
 (batch f).set (index i.val) (blockOf row) = batch (rowSet f i.val row) := by
 apply Subtype.ext
 apply List.ext_getElem?
 intro j
 have hi := index_val i.val (by omega)
 by_cases hj : j < 4
 · by_cases he : j = i.val
   · subst j
     simp [batch,AesInverseCircuit.originalBatch,Array.set,hi,List.getElem?_set,
       rowSet,i.isLt,blockOf]
   · simp [batch,AesInverseCircuit.originalBatch,Array.set,hi,List.getElem?_set,
       rowSet,hj,he,Ne.symm he,blockOf]
 · have hn : (batch (rowSet f i.val row)).val[j]? = none := List.getElem?_eq_none (by simp [batch,AesInverseCircuit.originalBatch]; omega)
   have hn' : ((batch f).set (index i.val) (blockOf row)).val[j]? = none := List.getElem?_eq_none (by simp [Array.set,batch,AesInverseCircuit.originalBatch]; omega)
   rw [hn,hn']

def progress (input data base : Nat → Nat → BitVec 8) (i n : Nat) :=
 rowSet base i (fun j => if j < n then input i j ^^^ data i j else 0)

theorem progress_row (input data base : Nat → Nat → BitVec 8) (i n : Nat) :
 blockOf (progress input data base i n i) = filled (input i) (data i) n := by
 unfold filled
 apply congrArg blockOf
 funext c
 simp [progress,rowSet]

theorem inner_progress (input data base : Nat → Nat → BitVec 8)
 (old : Array (Array U8 16#usize) 4#usize) (i : Fin 4) (j : Fin 16) :
 ActualParallelXor4.InOut.xor_in2out_loop0_loop0.body ⟨batch input,old⟩ (batch data)
  (index i.val) {start:=index j.val,«end»:=16#usize}
  (batch (progress input data base i.val j.val)) =
 .ok (.cont ({start:=index (j.val+1),«end»:=16#usize},
  batch (progress input data base i.val (j.val+1)))) := by
 rw [inner_step,progress_row,fill_next]
 simp only [filled]
 rw [batch_set]
 congr 3
 apply congrArg batch
 funext r c
 simp only [rowSet,progress]
 split <;> simp_all

theorem inner_done (input data base : Nat → Nat → BitVec 8)
 (old : Array (Array U8 16#usize) 4#usize) (i : Fin 4) (n : Nat) :
 ActualParallelXor4.InOut.xor_in2out_loop0_loop0.body ⟨batch input,old⟩ (batch data)
  (index i.val) {start:=index 16,«end»:=16#usize}
  (batch (progress input data base i.val n)) =
 .ok (.done (batch (progress input data base i.val n))) := by
 simp only [ActualParallelXor4.InOut.xor_in2out_loop0_loop0.body,range_done,
  uncurry_apply_pair,bind_tc_ok]

theorem inner_all (input data base : Nat → Nat → BitVec 8)
 (old : Array (Array U8 16#usize) 4#usize) (i : Fin 4) :
 ActualParallelXor4.InOut.xor_in2out_loop0_loop0 ⟨batch input,old⟩
  {start:=index 0,«end»:=16#usize} (batch data)
  (batch (progress input data base i.val 0)) (index i.val) =
 .ok (batch (progress input data base i.val 16)) := by
 simp only [ActualParallelXor4.InOut.xor_in2out_loop0_loop0]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [inner_progress input data base old i ⟨0,by decide⟩]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [inner_progress input data base old i ⟨1,by decide⟩]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [inner_progress input data base old i ⟨2,by decide⟩]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [inner_progress input data base old i ⟨3,by decide⟩]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [inner_progress input data base old i ⟨4,by decide⟩]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [inner_progress input data base old i ⟨5,by decide⟩]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [inner_progress input data base old i ⟨6,by decide⟩]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [inner_progress input data base old i ⟨7,by decide⟩]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [inner_progress input data base old i ⟨8,by decide⟩]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [inner_progress input data base old i ⟨9,by decide⟩]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [inner_progress input data base old i ⟨10,by decide⟩]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [inner_progress input data base old i ⟨11,by decide⟩]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [inner_progress input data base old i ⟨12,by decide⟩]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [inner_progress input data base old i ⟨13,by decide⟩]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [inner_progress input data base old i ⟨14,by decide⟩]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [inner_progress input data base old i ⟨15,by decide⟩]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [inner_done]

def outerFilled (input data : Nat → Nat → BitVec 8) (n : Nat) :=
 fun r c => if r < n ∧ c < 16 then input r c ^^^ data r c else 0

theorem progress_start (input data : Nat → Nat → BitVec 8) (i : Nat) :
 progress input data (outerFilled input data i) i 0 = outerFilled input data i := by
 funext r c
 by_cases h : r = i
 · subst r; simp [progress,rowSet,outerFilled]
 · simp [progress,rowSet,outerFilled,h]

theorem progress_finish (input data : Nat → Nat → BitVec 8) (i : Nat) :
 progress input data (outerFilled input data i) i 16 = outerFilled input data (i+1) := by
 funext r c
 by_cases h : r = i
 · subst r; simp [progress,rowSet,outerFilled]
 · have he : (r < i+1) ↔ (r < i) := by omega
   simp [progress,rowSet,outerFilled,h,he]

theorem outer_range_step (i : Fin 4) :
 core.iter.range.IteratorRange.next core.iter.range.StepUsize
  {start:=index i.val,«end»:=4#usize} =
 .ok (some (index i.val),{start:=index (i.val + 1),«end»:=4#usize}) := by
 have hi := index_val i.val (by omega)
 have h4 : (4#usize).val = 4 := rfl
 have h1 : (1#usize).val = 1 := rfl
 have hlt : (index i.val).val < (4#usize).val := by rw [hi,h4]; omega
 have hmax : (index i.val).val + (1#usize).val ≤ UScalar.max .Usize := by
  rw [hi,h1]
  scalar_tac
 have heq : UScalar.ofNatCore ((index i.val).val+(1#usize).val)
   (by scalar_tac) = index (i.val + 1) := by
  apply UScalar.eq_of_val_eq
  change (index i.val).val+(1#usize).val = (index (i.val + 1)).val
  rw [hi,h1,index_val _ (by omega)]
 simp only [core.iter.range.IteratorRange.next,core.iter.range.StepUsize,
  core.iter.range.UScalarStep,core.cmp.PartialOrdUsize,core.cmp.impls.PartialOrdUsize.lt,
  hlt,core.clone.CloneUsize,core.clone.impls.CloneUsize.clone,
  core.iter.range.UScalarStep.forward_checked,hmax,heq,lift,bind_tc_ok]
 simp

theorem outer_step (input data : Nat → Nat → BitVec 8)
 (old : Array (Array U8 16#usize) 4#usize) (i : Fin 4) :
 ActualParallelXor4.InOut.xor_in2out_loop0.body ⟨batch input,old⟩ (batch data)
  {start:=index i.val,«end»:=4#usize} (batch (outerFilled input data i.val)) =
 .ok (.cont ({start:=index (i.val+1),«end»:=4#usize},
  batch (outerFilled input data (i.val+1)))) := by
 have h := inner_all input data (outerFilled input data i.val) old i
 rw [progress_start,progress_finish] at h
 simp only [ActualParallelXor4.InOut.xor_in2out_loop0.body,outer_range_step,
  uncurry_apply_pair,bind_tc_ok]
 rw [← index_zero,h]
 rfl

theorem outer_range_done :
 core.iter.range.IteratorRange.next core.iter.range.StepUsize
  {start:=index 4,«end»:=4#usize} =
 .ok (none,{start:=index 4,«end»:=4#usize}) := by
 have hi := index_val 4 (by decide)
 have h4 : (4#usize).val = 4 := rfl
 simp [core.iter.range.IteratorRange.next,core.iter.range.StepUsize,
  core.iter.range.UScalarStep,core.cmp.PartialOrdUsize,core.cmp.impls.PartialOrdUsize.lt,hi,h4]

theorem outer_done (input data : Nat → Nat → BitVec 8)
 (old temp : Array (Array U8 16#usize) 4#usize) :
 ActualParallelXor4.InOut.xor_in2out_loop0.body ⟨batch input,old⟩ (batch data)
  {start:=index 4,«end»:=4#usize} temp = .ok (.done temp) := by
 simp only [ActualParallelXor4.InOut.xor_in2out_loop0.body,outer_range_done,
  uncurry_apply_pair,bind_tc_ok]

theorem outer_all (input data : Nat → Nat → BitVec 8)
 (old : Array (Array U8 16#usize) 4#usize) :
 ActualParallelXor4.InOut.xor_in2out_loop0 ⟨batch input,old⟩
  {start:=index 0,«end»:=4#usize} (batch data) (batch (outerFilled input data 0)) =
 .ok (batch (outerFilled input data 4)) := by
 simp only [ActualParallelXor4.InOut.xor_in2out_loop0]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [outer_step input data old ⟨0,by decide⟩]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [outer_step input data old ⟨1,by decide⟩]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [outer_step input data old ⟨2,by decide⟩]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [outer_step input data old ⟨3,by decide⟩]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [outer_done]

theorem batch_complete (input data : Nat → Nat → BitVec 8) :
 batch (outerFilled input data 4) = batch (fun r c => input r c ^^^ data r c) := by
 apply Subtype.ext
 simp only [batch,AesInverseCircuit.originalBatch,Subtype.coe_mk]
 apply List.map_congr_left
 intro r hr
 have hr' : r < 4 := by simpa using hr
 apply Subtype.ext
 simp only [blockOf,Subtype.coe_mk]
 apply List.map_congr_left
 intro c hc
 have hc' : c < 16 := by simpa using hc
 simp only [outerFilled,hr',hc',and_self,if_true]

theorem initial_batch (input data : Nat → Nat → BitVec 8) :
 batch (outerFilled input data 0) = batch (fun _ _ => 0) := by
 apply congrArg batch
 funext r c
 simp [outerFilled]

theorem source_xor (input data : Nat → Nat → BitVec 8)
 (old : Array (Array U8 16#usize) 4#usize) :
 ActualParallelXor4.InOut.xor_in2out ⟨batch input,old⟩ (batch data) =
 .ok (⟨batch input,batch (fun r c => input r c ^^^ data r c)⟩,
  (fun value => ⟨batch input,value.output⟩)) := by
 simp only [ActualParallelXor4.InOut.xor_in2out,FixedDispatch.default_batch,bind_tc_ok]
 have hzero := initial_batch input data
 unfold batch at hzero
 rw [←hzero,←index_zero]
 with_unfolding_all erw [outer_all]
 rw [← batch_complete input data]
 rfl

end LibSignalReference.Candidate.ParallelXor4
