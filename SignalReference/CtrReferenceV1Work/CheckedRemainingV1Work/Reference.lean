import CtrReferenceV1Work.CheckedRemainingV1Work.Generated.Funs
import CtrReferenceV1Work.FixedGeneratorV1Work.DriverReference
namespace LibSignalReference.Candidate.CheckedCtr16
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000

theorem ceil16 (value : Usize) :
 ∃ result, core.num.Usize.div_ceil value 16#usize = .ok result ∧
 result.val = value.val/16 + (if value.val%16 = 0 then 0 else 1) := by
 obtain ⟨d,hd,hv⟩ := UScalar.div_spec value (y:=16#usize) (by decide)
 obtain ⟨r,hr,rv⟩ := WP.spec_imp_exists (UScalar.rem_spec value (y:=16#usize) (by decide))
 change UScalar.div value 16#usize = .ok d at hd
 change UScalar.rem value 16#usize = .ok r at hr
 have hv' : d.val=value.val/16 := hv
 have rv' : r.val=value.val%16 := rv
 by_cases hzero : value.val%16=0
 · refine ⟨d,?_,?_⟩
   · with_unfolding_all simp only [core.num.Usize.div_ceil,hd,hr,bind_tc_ok]
     have h : ¬ (r > 0#usize) := by change ¬ (r.val > 0); rw [rv',hzero]; omega
     with_unfolding_all simp only [h,if_false]
   · simp only [hv',hzero,if_true,Nat.add_zero]
 · have h : r > 0#usize := by change r.val > 0; rw [rv']; omega
   have hbound : d.val + (1#usize).val ≤ UScalar.max .Usize := by
    have hmax : value.val ≤ UScalar.max .Usize := by scalar_tac
    have hquot := Nat.div_mul_le_self value.val 16
    rw [hv']
    change value.val/16 + 1 ≤ UScalar.max .Usize
    have hmin : 16 ≤ UScalar.max .Usize := by scalar_tac
    omega
   obtain ⟨next,hn,nv⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=d) (y:=1#usize) hbound)
   change UScalar.add d 1#usize = .ok next at hn
   refine ⟨next,?_,?_⟩
   · with_unfolding_all simp only [core.num.Usize.div_ceil,hd,hr,bind_tc_ok,h,if_true,hn]
   · simp only [hzero,if_false]
     change next.val = d.val + 1 at nv
     omega

def wrapper (counter : U32) (p : Fin 16) (tail : List U8) (ht : tail.length=15) :
 ActualCheckedCtr16.Wrapper :=
 ⟨⟨counter⟩,⟨(ReadBuffer16.physical (ReadBuffer16.cursor p) tail ht).buffer⟩⟩

theorem actual_core_remaining (counter : U32) :
 ∃ remaining, ActualCheckedCtr16.Core.remaining_blocks ⟨counter⟩ = .ok (some remaining) ∧
 remaining.val = 4294967295-counter.val := by
 obtain ⟨remaining,hr,hv⟩ := CtrStateRemaining.actual_body_remaining (CtrState.zeroNonce counter)
 refine ⟨remaining,?_,hv⟩
 simp only [ActualCheckedCtr16.Core.remaining_blocks,hr,bind_tc_ok,
  CtrStateRemaining.SomeRemaining]

theorem actual_buffer_remaining (counter : U32) (p : Fin 16) (tail : List U8) (ht : tail.length=15) :
 ActualCheckedCtr16.ReadBuffer.remaining (wrapper counter p tail ht).buffer =
 .ok (ReadBuffer16.available p) := by
 exact ReadBuffer16.remaining_actual p tail ht

theorem check_actual (counter : U32) (p : Fin 16) (tail : List U8) (ht : tail.length=15)
 (dataLen : Usize) :
 ActualCheckedCtr16.Wrapper.check_remaining (wrapper counter p tail ht) dataLen =
 .ok (if FixedCtr.requiredBlocks dataLen.val (15-p.val) ≤ 4294967295-counter.val
  then .Ok () else .Err ()) := by
 obtain ⟨remaining,hr,hv⟩ := actual_core_remaining counter
 simp only [ActualCheckedCtr16.Wrapper.check_remaining,wrapper,hr,bind_tc_ok]
 have hb := actual_buffer_remaining counter p tail ht
 change ActualCheckedCtr16.ReadBuffer.remaining ⟨(ReadBuffer16.physical (ReadBuffer16.cursor p) tail ht).buffer⟩ = _ at hb
 rw [hb]
 simp only [bind_tc_ok]
 by_cases hlt : dataLen.val < (ReadBuffer16.available p).val
 · have hs : (dataLen - (ReadBuffer16.available p) : Result Usize) = .fail .integerOverflow := by
    change UScalar.sub dataLen (ReadBuffer16.available p) = _
    simp only [UScalar.sub,hlt,if_true]
   simp only [Usize.checked_sub,core.num.checked_sub_UScalar,hs,Option.ofResult,lift,bind_tc_ok]
   have he : FixedCtr.requiredBlocks dataLen.val (15-p.val)=0 :=
    FixedCtr.cached_only _ _ (by rw [ReadBuffer16.available_val] at hlt; omega)
   simp only [he,Nat.zero_le,if_true]
 · obtain ⟨difference,hd,dv⟩ := WP.spec_imp_exists
    (UScalar.sub_spec (x:=dataLen) (y:=ReadBuffer16.available p) (by omega))
   simp only [Usize.checked_sub,core.num.checked_sub_UScalar,hd,Option.ofResult,lift,bind_tc_ok]
   obtain ⟨requested,hreq,rval⟩ := ceil16 difference
   rw [hreq]
   simp only [bind_tc_ok]
   have he : requested.val = FixedCtr.requiredBlocks dataLen.val (15-p.val) := by
    rw [dv.1,ReadBuffer16.available_val] at rval
    rw [FixedCtr.required_ceil]
    exact rval
   change (if requested.val > remaining.val then _ else _) = _
   rw [he,hv]
   split <;> split <;> simp_all <;> omega


theorem required_zero (bytes cached : Nat) :
 FixedCtr.requiredBlocks bytes cached = 0 ↔ bytes ≤ cached := by
 unfold FixedCtr.requiredBlocks
 omega

theorem check_exhausted (counter : U32) (maximum : counter.val=4294967295)
 (p : Fin 16) (tail : List U8) (ht : tail.length=15) (dataLen : Usize) :
 ActualCheckedCtr16.Wrapper.check_remaining (wrapper counter p tail ht) dataLen =
 .ok (if dataLen.val ≤ 15-p.val then .Ok () else .Err ()) := by
 rw [check_actual,maximum]
 have h : FixedCtr.requiredBlocks dataLen.val (15-p.val) ≤ 4294967295-4294967295 ↔
  dataLen.val ≤ 15-p.val := by
  simp only [Nat.sub_self,Nat.le_zero_eq,required_zero]
 simp only [h]

theorem accepted_no_wrap (counter : U32) (p : Fin 16) (tail : List U8)
 (ht : tail.length=15) (dataLen : Usize)
 (accepted : ActualCheckedCtr16.Wrapper.check_remaining (wrapper counter p tail ht) dataLen = .ok (.Ok ())) :
 counter.val + FixedCtr.requiredBlocks dataLen.val (15-p.val) ≤ 4294967295 := by
 rw [check_actual] at accepted
 have h : FixedCtr.requiredBlocks dataLen.val (15-p.val) ≤ 4294967295-counter.val := by
  split at accepted
  · assumption
  · cases accepted
 exact (FixedCtr.exact_remaining_guard _ _ _).mp h

end LibSignalReference.Candidate.CheckedCtr16
