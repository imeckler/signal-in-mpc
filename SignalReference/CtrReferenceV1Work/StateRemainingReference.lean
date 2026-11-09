import CtrReferenceV1Work.StateReference
import CtrReferenceV1Work.ConversionReference
namespace LibSignalReference.Candidate.CtrStateRemaining
open Aeneas Aeneas.Std
open LibSignalReference.Candidate.CtrState
open LibSignalReference.Candidate.CtrConversionV1
abbrev SomeRemaining := _root_.CtrStateV1.core.option.Option.specialized_Type_2455b8227f1e194b0fb8fba8e6015cc477b54ea44dfb19ba33823a6f9afbc8e4.Some
/-- Extracted remaining body; typed Std Result::ok is a stated success-path
external model. The widening operation is the actual previously generated leaf. -/
theorem actual_body_remaining (state : Nonce) :
  ∃ remaining, _root_.CtrStateV1.remaining state = .ok (SomeRemaining remaining) ∧
    remaining.val = 4294967295-state.ctr.val := by
  have bound : state.ctr.val ≤ core.num.U32.MAX.val := by rw [max_value]; scalar_tac
  obtain ⟨difference,hd,hv⟩ := WP.spec_imp_exists (U32.sub_spec (x:=core.num.U32.MAX) (y:=state.ctr) bound)
  refine ⟨UScalar.cast .Usize difference,?_,?_⟩
  · simp only [_root_.CtrStateV1.remaining,
      _root_.CtrStateV1.ctr.flavors.ctr32.Ctr32BE.Insts.CtrFlavorsCtrFlavorspecialized_Type_7a6a8388417110b23041d555c9b2b782ccc3704699a4bb3ba57a340304e5835c.remaining,
      hd, bind_tc_ok, _root_.CtrStateV1.U32.Insts.CoreConvertTryIntoUsize.try_into,
      actual_widen_ok,
      _root_.CtrStateV1.core.result.specialized_Type_39cefb7ef8c35a912b46372529760af6dab6d475787219ce914c64da40f08098.ok.specialized_Fun_a5d5674905ed002026d02685176bd5313ee0fdbe48d12a6d7a8a9a2595c3e604,SomeRemaining]
  · rw [U32.cast_Usize_val_eq, hv.1, max_value]

theorem exhaustion_exact (state : Nonce) :
  ∃ remaining, _root_.CtrStateV1.remaining state = .ok (SomeRemaining remaining) ∧
    (remaining.val=0 ↔ state.ctr.val=4294967295) := by
  obtain ⟨remaining,hr,hv⟩ := actual_body_remaining state
  refine ⟨remaining,hr,?_⟩
  have bound : state.ctr.val ≤ 4294967295 := by scalar_tac
  omega

theorem supported_blocks (state : Nonce) (n : Nat)
  (bound : state.ctr.val+n≤4294967295) :
  ∃ remaining, _root_.CtrStateV1.remaining state = .ok (SomeRemaining remaining) ∧ n≤remaining.val := by
  obtain ⟨remaining,hr,hv⟩ := actual_body_remaining state
  exact ⟨remaining,hr,by omega⟩
end LibSignalReference.Candidate.CtrStateRemaining
