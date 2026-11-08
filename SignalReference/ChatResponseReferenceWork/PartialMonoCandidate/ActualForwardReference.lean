import ChatResponseReferenceWork.PartialMonoCandidate.GeneratedForwardActual.Funs
open Aeneas Aeneas.Std Result
namespace ActualBufForward
/-- All outcomes of the actual native mutable Buf forwarding implementation,
under its observed receiver projection. The auxiliary backward map is executed,
not discarded. No callback correctness or successful execution is assumed. -/
theorem forward_all_outcomes {B : Type} (inst : bytes.buf.buf_impl.Buf B)
    (input : B) (n : Usize) :
    forward_actual inst input n = inst.advance input n := by
  unfold forward_actual bytes.buf.buf_impl.Buf.partial_TraitDecl_1.Blanket.advance
  cases h : inst.advance input n <;> rfl
/-- The actual generated helper preserves the exact updated receiver and its
identity backward continuation, before the outer observation is applied. -/
theorem raw_forward_success {B : Type} (inst : bytes.buf.buf_impl.Buf B)
    (input after : B) (n : Usize) (h : inst.advance input n = .ok after) :
    bytes.buf.buf_impl.Buf.partial_TraitDecl_1.Blanket.advance inst input n =
      .ok (after, fun final => final) := by
  unfold bytes.buf.buf_impl.Buf.partial_TraitDecl_1.Blanket.advance
  rw [h]
  rfl
#print axioms forward_all_outcomes
#print axioms raw_forward_success
end ActualBufForward
