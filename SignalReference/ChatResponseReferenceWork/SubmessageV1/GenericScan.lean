import ChatResponseReferenceWork.SubmessageV1.Reference
import ChatResponseReferenceWork.InnerScanV1.Totality
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.SubmessageGenericV1
open ActualSubmessageV1
abbrev sliceBuf := InnerResponseV1.sliceBuf
noncomputable def callback {M : Type} (mi : prost.message.Message M) :=
  prost.encoding.message.merge.closure.Insts.CoreOpsFunctionFnMutTupleMutMMutBDecodeContextResultTupleDecodeError mi sliceBuf
/-- An intermediate consumption interface, discharged by actual generated field
proofs at every exported schema instantiation. It asserts no field validity. -/
def FieldBound {M : Type} (mi : prost.message.Message M) : Prop :=
  ∀ (state next : M) tag wire (before after : Slice U8) ctx status,
    mi.merge_field sliceBuf state tag wire before ctx = .ok (status,next,after) →
      after.length ≤ before.length

theorem key_exact (before : Slice U8) :
    prost.encoding.decode_key sliceBuf before =
      ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before := rfl

theorem callback_consumption {M : Type} (mi : prost.message.Message M) (fields : FieldBound mi)
    (ctx : prost.encoding.DecodeContext) (state next : M) (before after : Slice U8)
    (status : core.result.Result Unit prost.error.DecodeError)
    (observed : (callback mi).call_mut () (state,before,ctx) = .ok (status,(),next,after)) :
    after.length ≤ before.length ∧ (status = .Ok () → after.length < before.length) := by
  change (do
    let (result,value,suffix,closure) ← Raw.prost.encoding.message.merge.closure.Insts.CoreOpsFunctionFnMutTupleMutMMutBDecodeContextResultTupleDecodeError.call_mut mi sliceBuf () (state,before,ctx)
    .ok (result,closure,value,suffix)) = .ok (status,(),next,after) at observed
  unfold Raw.prost.encoding.message.merge.closure.Insts.CoreOpsFunctionFnMutTupleMutMMutBDecodeContextResultTupleDecodeError.call_mut at observed
  dsimp! only at observed
  obtain ⟨key,middle,keyRun,actualKey,bound,strict⟩ := InnerScanV1.key_total before
  rw [key_exact,actualKey] at observed
  cases key with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from] at observed
    rcases observed with ⟨rfl,rfl,rfl⟩
    exact ⟨bound,by intro impossible; cases impossible⟩
  | Ok pair =>
    rcases pair with ⟨tag,wire⟩
    have keyStrict := strict (tag,wire) rfl
    simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch] at observed
    dsimp! only at observed
    cases fieldRun : mi.merge_field sliceBuf state tag (ActualResponseBytesV1.fromSkipWire wire) middle ctx with
    | fail error => simp [fieldRun] at observed
    | div => simp [fieldRun] at observed
    | ok output =>
      rcases output with ⟨result,value,suffix⟩
      have fieldBound := fields state value tag (ActualResponseBytesV1.fromSkipWire wire) middle suffix ctx result fieldRun
      simp [fieldRun] at observed
      rcases observed with ⟨rfl,rfl,rfl⟩
      exact ⟨fieldBound.trans bound,fun _ => fieldBound.trans_lt keyStrict⟩

noncomputable def body {M : Type} (mi : prost.message.Message M)
    (ctx : prost.encoding.DecodeContext) (limit : Usize) (state : M × Slice U8 × Unit) :=
  prost.encoding.merge_loop_loop.body (callback mi) sliceBuf ctx limit state.1 state.2.1 state.2.2

theorem body_decreases {M : Type} (mi : prost.message.Message M) (fields : FieldBound mi)
    (ctx : prost.encoding.DecodeContext) (limit : Usize) (state next : M × Slice U8 × Unit)
    (continued : body mi ctx limit state = .ok (.cont next)) :
    next.2.1.length < state.2.1.length := by
  rcases state with ⟨state,before,closure⟩
  rcases next with ⟨next,after,nextClosure⟩
  cases closure
  cases nextClosure
  unfold body prost.encoding.merge_loop_loop.body at continued
  rw [show Mut0T.Insts.BytesBufBuf_implBuf.remaining sliceBuf before = .ok before.len from rfl] at continued
  simp only [bind_tc_ok] at continued
  split at continued
  · rw [show prost.encoding.DecodeContext.Insts.CoreCloneClone.clone ctx = .ok ctx from InnerScanV1.clone_ctx ctx] at continued
    simp only [bind_tc_ok] at continued
    cases called : (callback mi).call_mut () (state,before,ctx) with
    | fail error => simp [called] at continued
    | div => simp [called] at continued
    | ok output =>
      rcases output with ⟨status,closure,value,suffix⟩
      cases closure
      cases status with
      | Err error => simp [called,core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from] at continued
      | Ok unit =>
        simp [called,core.result.Result.Insts.CoreOpsTry.branch] at continued
        rcases continued with ⟨rfl,rfl⟩
        exact (callback_consumption mi fields ctx state value before suffix (.Ok ()) called).2 rfl
  · split at continued
    · simp [core.convert.IntoFrom.into,prost.error.DecodeError.Insts.CoreConvertFromDecodeErrorKind.from] at continued
    · cases continued

theorem actual_scan_finite {M : Type} (mi : prost.message.Message M) (fields : FieldBound mi)
    (ctx : prost.encoding.DecodeContext) (limit : Usize) (state : M) (before : Slice U8) :
    ∃ result, InnerScanV1.FiniteRun (body mi ctx limit) (state,before,()) result ∧
      prost.encoding.merge_loop_loop (callback mi) sliceBuf state before ctx () limit = result := by
  obtain ⟨result,run⟩ := InnerScanV1.finite_run_exists (body mi ctx limit)
    (fun pair => pair.2.1.length) (body_decreases mi fields ctx limit) (state,before,())
  exact ⟨result,run,InnerScanV1.finite_run_actual run⟩
#print axioms callback_consumption
#print axioms actual_scan_finite
end ChatResponseReference.SubmessageGenericV1
