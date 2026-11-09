import CtrReferenceV1Work.Generated.ConversionFinal.Funs
namespace LibSignalReference.Candidate.CtrConversionV1
open Aeneas Aeneas.Std
open CtrConversionV1
theorem max_value : core.num.U32.MAX.val=4294967295 := by decide
/-- The unchanged actual conversion called by ctr0.10.1's remaining(). -/
theorem actual_widen_ok (value : U32) :
 CtrConversionV1.Usize.Insts.CoreConvertTryFromU32TryFromIntError.try_from value =
  .ok (.Ok (UScalar.cast .Usize value)) := by rfl

theorem actual_widen_value (value : U32) :
 ∃ result, CtrConversionV1.Usize.Insts.CoreConvertTryFromU32TryFromIntError.try_from value = .ok (.Ok result) ∧ result.val=value.val := by
 exact ⟨UScalar.cast .Usize value,actual_widen_ok value,U32.cast_Usize_val_eq value⟩

-- The first two operations of actual remaining() (checked subtraction followed
-- by its actual generated conversion). Full remaining()/Result::ok translation
-- and its success-path specialization remain separate source obligations.
def remainingPrefix (counter : U32) : Result (core.result.Result Usize core.num.error.TryFromIntError) := do
 let difference ← core.num.U32.MAX - counter
 CtrConversionV1.Usize.Insts.CoreConvertTryFromU32TryFromIntError.try_from difference

theorem remaining_prefix_success (counter : U32) :
 ∃ result, remainingPrefix counter = .ok (.Ok result) ∧ result.val=4294967295-counter.val := by
 have bound : counter.val ≤ core.num.U32.MAX.val := by rw [max_value];scalar_tac
 obtain ⟨difference,hd,hv⟩ := WP.spec_imp_exists (U32.sub_spec (x:=core.num.U32.MAX) (y:=counter) bound)
 obtain ⟨result,hr,hval⟩ := actual_widen_value difference
 refine ⟨result,?_,?_⟩
 · simp only [remainingPrefix,hd,bind_tc_ok,hr]
 · rw [hval,hv.1,max_value]

theorem remaining_prefix_never_err (counter : U32) (error : core.num.error.TryFromIntError) :
 remainingPrefix counter ≠ .ok (.Err error) := by
 obtain ⟨result,hr,_⟩ := remaining_prefix_success counter
 rw [hr];intro impossible;cases impossible

theorem exhaustion_exact (counter : U32) :
 ∃ result, remainingPrefix counter = .ok (.Ok result) ∧
  (result.val=0 ↔ counter.val=4294967295) := by
 obtain ⟨result,hr,hv⟩ := remaining_prefix_success counter
 refine ⟨result,hr,?_⟩
 have bound : counter.val≤4294967295 := by scalar_tac
 omega

theorem bounded_ss_blocks (bytes : Nat) (bound : bytes≤8192) :
 (bytes+15)/16≤512 ∧ 512≤4294967295 := by omega

theorem initial_counter_capacity (counter : U32) (zero : counter.val=0)
 (bytes : Nat) (bound : bytes≤8192) :
 ∃ result, remainingPrefix counter=.ok (.Ok result) ∧ (bytes+15)/16≤result.val := by
 obtain ⟨result,hr,hv⟩ := remaining_prefix_success counter
 have := (bounded_ss_blocks bytes bound).1
 exact ⟨result,hr,by rw [zero] at hv;omega⟩
end LibSignalReference.Candidate.CtrConversionV1
