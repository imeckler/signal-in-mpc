import ChatResponseReferenceWork.PartialMonoCandidate.ActualForwardReference
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.TypedLoanProjection
/-- A typed bridge between a standalone translated borrow helper and its trait
field operation. Applying the backward continuation is part of the observation;
the two views must commute for every result, including failure and divergence. -/
structure LoanOp (B N : Type) where
  raw : B → N → Result (B × (B → B))
  observed : B → N → Result B
  correspondence : ∀ input n, (do
    let (after, restore) ← raw input n
    .ok (restore after)) = observed input n
instance {B N : Type} : CoeFun (LoanOp B N) (fun _ => B → N → Result (B × (B → B))) :=
  ⟨LoanOp.raw⟩
instance {B N : Type} : Coe (LoanOp B N) (B → N → Result B) :=
  ⟨LoanOp.observed⟩
/-- The raw call preserves the complete auxiliary return. -/
theorem raw_view {B N : Type} (operation : LoanOp B N) (input : B) (n : N) :
    operation input n = operation.raw input n := rfl
/-- The trait-field view executes the raw backward continuation. -/
theorem field_view {B N : Type} (operation : LoanOp B N) (input : B) (n : N) :
    (operation : B → N → Result B) input n = (do
      let (after, restore) ← operation.raw input n
      .ok (restore after)) := (operation.correspondence input n).symm
/-- A native outer failure is never converted into success by the bridge. -/
theorem failure_exact {B N : Type} (operation : LoanOp B N) (input : B) (n : N)
    (error : Error) (h : operation.raw input n = .fail error) :
    operation.observed input n = .fail error := by
  rw [← operation.correspondence input n,h]
  rfl
def actualAdvance {B : Type} (inst : ActualBufForward.bytes.buf.buf_impl.Buf B) : LoanOp B Usize where
  raw := ActualBufForward.bytes.buf.buf_impl.Buf.partial_TraitDecl_1.Blanket.advance inst
  observed := inst.advance
  correspondence := ActualBufForward.forward_all_outcomes inst
/-- Same expected field type as the generated mutable Buf trait. The explicit
wrapper is the only type subject to this coercion; arbitrary functions acquire
no implicit projection. -/
structure AdvanceField (B : Type) where
  advance : B → Usize → Result B
def actualField {B : Type} (inst : ActualBufForward.bytes.buf.buf_impl.Buf B) : AdvanceField B :=
  ⟨actualAdvance inst⟩
theorem actual_field_exact {B : Type} (inst : ActualBufForward.bytes.buf.buf_impl.Buf B) :
    (actualField inst).advance = inst.advance := rfl
#print axioms field_view
#print axioms failure_exact
#print axioms actual_field_exact
end ChatResponseReference.TypedLoanProjection
