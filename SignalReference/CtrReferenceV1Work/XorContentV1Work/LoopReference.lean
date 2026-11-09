import CtrReferenceV1Work.XorContentV1Work.GeneratedSelected.Funs
import AesCtrBlockWork.FixedDispatchV1Work.WrapperReference
namespace LibSignalReference.Candidate.XorContent16
open Aeneas Aeneas.Std
open LibSignalReference.Candidate.FixedDispatch
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def index (n : Nat) : Usize := ⟨BitVec.ofNat _ n⟩
theorem index_val (n : Nat) (bound : n ≤ 16) : (index n).val = n := by
 simp only [index,UScalar.val,BitVec.toNat_ofNat,UScalarTy.numBits]
 apply Nat.mod_eq_of_lt
 rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> norm_num <;> omega

theorem range_step (i : Fin 16) :
 core.iter.range.IteratorRange.next core.iter.range.StepUsize
  {start:=index i.val,«end»:=16#usize} =
 .ok (some (index i.val),{start:=index (i.val + 1),«end»:=16#usize}) := by
 have hi := index_val i.val (by omega)
 have h16 : (16#usize).val = 16 := rfl
 have h1 : (1#usize).val = 1 := rfl
 have hlt : (index i.val).val < (16#usize).val := by rw [hi,h16]; omega
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

theorem block_index (input : Nat → BitVec 8) (i : Fin 16) :
 Array.index_usize (blockOf input) (index i.val) = .ok (⟨input i.val⟩ : U8) := by
 have hi := index_val i.val (by omega)
 simp [Array.index_usize,blockOf,hi,i.isLt]

theorem byte_xor (a b : BitVec 8) :
 ((⟨a⟩ : U8) ^^^ ⟨b⟩) = (⟨a ^^^ b⟩ : U8) := rfl

theorem update_valid (temp : Array U8 16#usize) (i : Fin 16) (fresh : U8) :
 Array.update temp (index i.val) fresh = .ok (temp.set (index i.val) fresh) := by
 have hi := index_val i.val (by omega)
 obtain ⟨next,hcall,hnext⟩ := WP.spec_imp_exists
  (Array.update_spec temp (index i.val) fresh (by simp only [Array.length,Array.length_eq,hi]; change i.val<16; omega))
 simpa only [hnext] using hcall

theorem body_step (input data : Nat → BitVec 8) (old temp : Array U8 16#usize) (i : Fin 16) :
 ActualXorContent16.InOut.xor_in2out_loop.body ⟨blockOf input,old⟩ (blockOf data)
  {start:=index i.val,«end»:=16#usize} temp =
 .ok (.cont ({start:=index (i.val + 1),«end»:=16#usize},
  temp.set (index i.val) (⟨input i.val ^^^ data i.val⟩ : U8))) := by
 simp only [ActualXorContent16.InOut.xor_in2out_loop.body,range_step,
  uncurry_apply_pair,bind_tc_ok,block_index,byte_xor,lift,update_valid]

theorem range_done :
 core.iter.range.IteratorRange.next core.iter.range.StepUsize
  {start:=index 16,«end»:=16#usize} =
 .ok (none,{start:=index 16,«end»:=16#usize}) := by
 have hi := index_val 16 (by decide)
 have h16 : (16#usize).val = 16 := rfl
 simp [core.iter.range.IteratorRange.next,core.iter.range.StepUsize,
  core.iter.range.UScalarStep,core.cmp.PartialOrdUsize,core.cmp.impls.PartialOrdUsize.lt,hi,h16]

theorem body_done (input data : Nat → BitVec 8) (old temp : Array U8 16#usize) :
 ActualXorContent16.InOut.xor_in2out_loop.body ⟨blockOf input,old⟩ (blockOf data)
  {start:=index 16,«end»:=16#usize} temp = .ok (.done temp) := by
 simp only [ActualXorContent16.InOut.xor_in2out_loop.body,range_done,
  uncurry_apply_pair,bind_tc_ok]

def filled (input data : Nat → BitVec 8) (n : Nat) : Array U8 16#usize :=
 blockOf (fun j => if j < n then input j ^^^ data j else 0)

theorem fill_next (input data : Nat → BitVec 8) (i : Fin 16) :
 (filled input data i.val).set (index i.val) (⟨input i.val ^^^ data i.val⟩ : U8) =
 filled input data (i.val + 1) := by
 apply Subtype.ext
 apply List.ext_getElem?
 intro j
 have hidx := index_val i.val (by omega)
 by_cases hj : j < 16
 · by_cases he : j=i.val
   · subst j
     simp [Array.set,filled,blockOf,hidx,List.getElem?_set,i.isLt]
   · have hiff : (j < i.val) ↔ (j < i.val + 1) := by omega
     simp [Array.set,filled,blockOf,hidx,List.getElem?_set,hj,he,Ne.symm he,hiff]
 · have hl : ((filled input data i.val).set (index i.val)
    (⟨input i.val ^^^ data i.val⟩ : U8)).val.length = 16 := by
    simpa using ((filled input data i.val).set (index i.val)
     (⟨input i.val ^^^ data i.val⟩ : U8)).property
   have hr : (filled input data (i.val + 1)).val.length = 16 := by
    simpa using (filled input data (i.val + 1)).property
   have hnoneL : ((filled input data i.val).set (index i.val)
    (⟨input i.val ^^^ data i.val⟩ : U8)).val[j]? = none := List.getElem?_eq_none (by omega)
   have hnoneR : (filled input data (i.val + 1)).val[j]? = none := List.getElem?_eq_none (by omega)
   rw [hnoneL,hnoneR]

theorem filled_complete (input data : Nat → BitVec 8) :
 filled input data 16 = blockOf (fun i => input i ^^^ data i) := by
 apply Subtype.ext
 simp only [filled,blockOf,Subtype.coe_mk]
 apply List.map_congr_left
 intro j hj
 have h : j < 16 := by simpa using hj
 simp only [h,if_true]

theorem index_zero : index 0 = 0#usize := by
 apply UScalar.eq_of_val_eq
 rw [index_val 0 (by decide)]
 rfl

theorem default_block (input data : Nat → BitVec 8) :
 core.default.DefaultArray.default 16#usize core.default.DefaultU8 = .ok (filled input data 0) := by
 simp [core.default.DefaultArray.default,core.default.DefaultU8.default,
  Array.repeat,filled,blockOf,List.range_succ,UScalar.ofNatCore]
 simp only [UScalar.val]
 rfl

theorem loop_all (input data : Nat → BitVec 8) (old : Array U8 16#usize) :
 ActualXorContent16.InOut.xor_in2out_loop ⟨blockOf input,old⟩
  {start:=index 0,«end»:=16#usize} (blockOf data) (filled input data 0) =
 .ok (blockOf (fun i => input i ^^^ data i)) := by
 simp only [ActualXorContent16.InOut.xor_in2out_loop]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [body_step input data old (filled input data 0) ⟨0,by decide⟩]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [fill_next input data ⟨0,by decide⟩]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [body_step input data old (filled input data 1) ⟨1,by decide⟩]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [fill_next input data ⟨1,by decide⟩]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [body_step input data old (filled input data 2) ⟨2,by decide⟩]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [fill_next input data ⟨2,by decide⟩]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [body_step input data old (filled input data 3) ⟨3,by decide⟩]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [fill_next input data ⟨3,by decide⟩]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [body_step input data old (filled input data 4) ⟨4,by decide⟩]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [fill_next input data ⟨4,by decide⟩]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [body_step input data old (filled input data 5) ⟨5,by decide⟩]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [fill_next input data ⟨5,by decide⟩]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [body_step input data old (filled input data 6) ⟨6,by decide⟩]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [fill_next input data ⟨6,by decide⟩]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [body_step input data old (filled input data 7) ⟨7,by decide⟩]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [fill_next input data ⟨7,by decide⟩]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [body_step input data old (filled input data 8) ⟨8,by decide⟩]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [fill_next input data ⟨8,by decide⟩]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [body_step input data old (filled input data 9) ⟨9,by decide⟩]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [fill_next input data ⟨9,by decide⟩]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [body_step input data old (filled input data 10) ⟨10,by decide⟩]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [fill_next input data ⟨10,by decide⟩]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [body_step input data old (filled input data 11) ⟨11,by decide⟩]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [fill_next input data ⟨11,by decide⟩]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [body_step input data old (filled input data 12) ⟨12,by decide⟩]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [fill_next input data ⟨12,by decide⟩]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [body_step input data old (filled input data 13) ⟨13,by decide⟩]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [fill_next input data ⟨13,by decide⟩]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [body_step input data old (filled input data 14) ⟨14,by decide⟩]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [fill_next input data ⟨14,by decide⟩]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [body_step input data old (filled input data 15) ⟨15,by decide⟩]
 simp only [bind_tc_ok,uncurry_apply_pair]
 rw [fill_next input data ⟨15,by decide⟩]
 rw [loop.eq_1]
 simp only [uncurry_apply_pair]
 rw [body_done]
 simp only [bind_tc_ok]
 exact congrArg Result.ok (filled_complete input data)

theorem source_xor (input data : Nat → BitVec 8) (old : Array U8 16#usize) :
 ActualXorContent16.InOut.xor_in2out ⟨blockOf input,old⟩ (blockOf data) =
 .ok (⟨blockOf input,blockOf (fun i => input i ^^^ data i)⟩,
  (fun value => ⟨blockOf input,value.output⟩)) := by
 simp only [ActualXorContent16.InOut.xor_in2out,default_block input data,bind_tc_ok]
 rw [←index_zero,loop_all]
 rfl

end LibSignalReference.Candidate.XorContent16
