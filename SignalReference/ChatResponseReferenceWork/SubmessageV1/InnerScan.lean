import ChatResponseReferenceWork.SubmessageV1.Reference
import ChatResponseReferenceWork.InnerScanV1.Totality
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.SubmessageV1
open ActualSubmessageV1
abbrev Message := InnerScanV1.Message
noncomputable def schema : prost.message.Message Message := {
  encode_raw := fun _ _ _ => .fail .undef
  merge_field := fun inst state tag wire before ctx =>
    ActualInnerResponseV1.merge_response inst state tag wire before ctx
  encoded_len := fun _ => .fail .undef
  clear := fun _ => .fail .undef }
abbrev sliceBuf := InnerResponseV1.sliceBuf
noncomputable abbrev callback :=
  prost.encoding.message.merge.closure.Insts.CoreOpsFunctionFnMutTupleMutMMutBDecodeContextResultTupleDecodeError schema sliceBuf

theorem key_exact (before : Slice U8) :
    prost.encoding.decode_key sliceBuf before =
      ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before := rfl

/-- The actual generated callback first consumes a successful key and then the
actual generated inner field. Every successful callback strictly consumes input. -/
theorem callback_decreases (ctx : prost.encoding.DecodeContext) (state next : Message)
    (before after : Slice U8)
    (observed : callback.call_mut () (state,before,ctx) = .ok (.Ok (),(),next,after)) :
    after.length < before.length := by
  change (do
    let (result,value,suffix,closure) ← Raw.prost.encoding.message.merge.closure.Insts.CoreOpsFunctionFnMutTupleMutMMutBDecodeContextResultTupleDecodeError.call_mut schema sliceBuf () (state,before,ctx)
    .ok (result,closure,value,suffix)) = .ok (.Ok (),(),next,after) at observed
  unfold Raw.prost.encoding.message.merge.closure.Insts.CoreOpsFunctionFnMutTupleMutMMutBDecodeContextResultTupleDecodeError.call_mut at observed
  dsimp! only at observed
  obtain ⟨key,middle,keyRun,actualKey,bound,strict⟩ := InnerScanV1.key_total before
  rw [key_exact,actualKey] at observed
  cases key with
  | Err error => cases observed
  | Ok pair =>
    rcases pair with ⟨tag,wire⟩
    have keyStrict := strict (tag,wire) rfl
    simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,schema,InnerResponseV1.dispatcher_reference] at observed
    dsimp! only at observed
    cases fieldRun : InnerResponseV1.fieldSpec sliceBuf state tag
        (ActualResponseBytesV1.fromSkipWire wire) middle ctx with
    | fail error => simp [fieldRun] at observed
    | div => simp [fieldRun] at observed
    | ok output =>
      rcases output with ⟨result,value,suffix⟩
      have fieldBound := InnerScanV1.field_consumption state value tag
        (ActualResponseBytesV1.fromSkipWire wire) middle suffix ctx result fieldRun
      cases result with
      | Err error => simp [fieldRun] at observed
      | Ok unit =>
        simp [fieldRun] at observed
        rcases observed with ⟨rfl,rfl⟩
        exact fieldBound.trans_lt keyStrict
noncomputable def body (ctx : prost.encoding.DecodeContext) (limit : Usize)
    (state : Message × Slice U8 × Unit) :=
  prost.encoding.merge_loop_loop.body callback sliceBuf ctx limit state.1 state.2.1 state.2.2

theorem body_decreases (ctx : prost.encoding.DecodeContext) (limit : Usize)
    (state next : Message × Slice U8 × Unit)
    (continued : body ctx limit state = .ok (.cont next)) :
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
    cases called : FnMutBorrowV1.toTrait
        ((prost.encoding.message.merge.closure.Insts.CoreOpsFunctionFnMutTupleMutMMutBDecodeContextResultTupleDecodeError.call_mut schema sliceBuf).raw
          () (state,before,ctx)) with
    | fail error => simp [called] at continued
    | div => simp [called] at continued
    | ok output =>
      rcases output with ⟨status,closure,value,suffix⟩
      cases closure
      cases status with
      | Err error => simp [called,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from] at continued
      | Ok unit =>
        simp [called,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from] at continued
        rcases continued with ⟨rfl,rfl⟩
        exact callback_decreases ctx state value before suffix called
  · split at continued
    · simp [core.convert.IntoFrom.into,
        prost.error.DecodeError.Insts.CoreConvertFromDecodeErrorKind.from] at continued
    · cases continued

/-- Actual length-delimited inner response loop, with the real parent remaining
limit, has finite execution. The proof includes overrun/error/outer fail/div;
there is no assumption that field callbacks stop at the declared child end. -/
theorem actual_delimited_scan_finite (ctx : prost.encoding.DecodeContext) (limit : Usize)
    (state : Message) (before : Slice U8) :
    ∃ result,
      InnerScanV1.FiniteRun (body ctx limit) (state,before,()) result ∧
      prost.encoding.merge_loop_loop callback sliceBuf state before ctx () limit = result := by
  obtain ⟨result,run⟩ := InnerScanV1.finite_run_exists (body ctx limit)
    (fun pair => pair.2.1.length) (body_decreases ctx limit) (state,before,())
  exact ⟨result,run,InnerScanV1.finite_run_actual run⟩
#print axioms body_decreases
#print axioms actual_delimited_scan_finite
#print axioms key_exact
#print axioms callback_decreases
end ChatResponseReference.SubmessageV1
