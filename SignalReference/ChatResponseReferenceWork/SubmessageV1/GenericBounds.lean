import ChatResponseReferenceWork.SubmessageV1.GenericScan
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.SubmessageGenericV1
open ActualSubmessageV1

theorem body_done_bound {M : Type} (mi : prost.message.Message M) (fields : FieldBound mi)
    (ctx : prost.encoding.DecodeContext) (limit : Usize) (state : M × Slice U8 × Unit)
    (result : core.result.Result Unit prost.error.DecodeError × M × Slice U8)
    (finished : body mi ctx limit state = .ok (.done result)) :
    result.2.2.length ≤ state.2.1.length := by
  rcases state with ⟨state,before,closure⟩
  rcases result with ⟨status,next,after⟩
  cases closure
  unfold body prost.encoding.merge_loop_loop.body at finished
  rw [show Mut0T.Insts.BytesBufBuf_implBuf.remaining sliceBuf before = .ok before.len from rfl] at finished
  simp only [bind_tc_ok] at finished
  split at finished
  · rw [show prost.encoding.DecodeContext.Insts.CoreCloneClone.clone ctx = .ok ctx from InnerScanV1.clone_ctx ctx] at finished
    simp only [bind_tc_ok] at finished
    cases called : (callback mi).call_mut () (state,before,ctx) with
    | fail error => simp [called] at finished
    | div => simp [called] at finished
    | ok output =>
      rcases output with ⟨status,closure,value,suffix⟩
      cases closure
      cases status with
      | Ok unit => simp [called,core.result.Result.Insts.CoreOpsTry.branch] at finished
      | Err error =>
        simp [called,core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from] at finished
        rcases finished with ⟨rfl,rfl,rfl⟩
        exact (callback_consumption mi fields ctx state value before suffix (.Err error) called).1
  · split at finished
    · simp [core.convert.IntoFrom.into,prost.error.DecodeError.Insts.CoreConvertFromDecodeErrorKind.from] at finished
      rcases finished with ⟨rfl,rfl,rfl⟩
      exact Nat.le_refl _
    · simp at finished
      rcases finished with ⟨rfl,rfl,rfl⟩
      exact Nat.le_refl _

theorem finite_run_bound {M : Type} (mi : prost.message.Message M) (fields : FieldBound mi)
    (ctx : prost.encoding.DecodeContext) (limit : Usize) {state outcome}
    (run : InnerScanV1.FiniteRun (body mi ctx limit) state outcome) :
    ∀ result, outcome = .ok result → result.2.2.length ≤ state.2.1.length := by
  induction run with
  | done step => intro result same; cases same; exact body_done_bound mi fields ctx limit _ _ step
  | fail step => intro result impossible; cases impossible
  | div step => intro result impossible; cases impossible
  | next step rest ih =>
    intro result same
    exact (ih result same).trans (Nat.le_of_lt (body_decreases mi fields ctx limit _ _ step))

/-- Every ordinary returned inner result, including malformed/error outcomes,
keeps a suffix of no greater length than the actual parent input. -/
theorem actual_loop_bound {M : Type} (mi : prost.message.Message M) (fields : FieldBound mi)
    (ctx : prost.encoding.DecodeContext) (limit : Usize) (state : M) (before : Slice U8)
    (result : core.result.Result Unit prost.error.DecodeError × M × Slice U8)
    (observed : prost.encoding.merge_loop_loop (callback mi) sliceBuf state before ctx () limit = .ok result) :
    result.2.2.length ≤ before.length := by
  obtain ⟨outcome,run,actual⟩ := actual_scan_finite mi fields ctx limit state before
  rw [actual] at observed
  exact finite_run_bound mi fields ctx limit run result observed
#print axioms body_done_bound
#print axioms actual_loop_bound
end ChatResponseReference.SubmessageGenericV1
