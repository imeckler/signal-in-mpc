import ChatResponseReferenceWork.SubmessageV1.GenericBounds
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.SubmessageGenericV1
open ActualSubmessageV1

def decodedResult (decoded : core.result.Result U64 LoopSupportSkip.error.DecodeError) :
    core.result.Result U64 prost.error.DecodeError :=
  match decoded with
  | .Ok value => .Ok value
  | .Err error => .Err (ActualResponseBytesV1.fromSkipError error)

theorem varint_exact (before after : Slice U8)
    (decoded : core.result.Result U64 LoopSupportSkip.error.DecodeError)
    (run : LoopSupportSkip.encoding.varint.decode_varint LibSignalReference.Candidate.ProstSkipBuf.sliceBuf before = .ok (decoded,after)) :
    prost.encoding.varint.decode_varint sliceBuf before = .ok (decodedResult decoded,after) := by
  unfold prost.encoding.varint.decode_varint ActualInnerResponseV1.prost.encoding.varint.decode_varint
    ActualResponseBytesV1.prost.encoding.varint.decode_varint
  rw [InnerResponseV1.scalar_adapter,run]
  cases decoded <;> rfl

/-- Length-prefix underflow/errors and the real parent-limit loop all preserve a
nonincreasing suffix on ordinary return. Arithmetic fail/div remain unchanged. -/
theorem merge_loop_bound {M : Type} (mi : prost.message.Message M) (fields : FieldBound mi)
    (ctx : prost.encoding.DecodeContext) (state next : M) (before after : Slice U8)
    (status : core.result.Result Unit prost.error.DecodeError)
    (observed : prost.encoding.merge_loop (callback mi) sliceBuf state before ctx () = .ok (status,next,after)) :
    after.length ≤ before.length := by
  obtain ⟨decoded,middle,run,bound,strict⟩ := FullParserV3.varint_total before
  unfold prost.encoding.merge_loop at observed
  rw [varint_exact before middle decoded run] at observed
  cases decoded with
  | Err error =>
    simp [decodedResult,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from] at observed
    rcases observed with ⟨rfl,rfl,rfl⟩
    exact bound
  | Ok value =>
    simp only [decodedResult,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch] at observed
    dsimp! only at observed
    rw [show Mut0T.Insts.BytesBufBuf_implBuf.remaining sliceBuf middle = .ok middle.len from rfl] at observed
    simp only [lift,bind_tc_ok] at observed
    split at observed
    · simp [core.convert.IntoFrom.into,prost.error.DecodeError.Insts.CoreConvertFromDecodeErrorKind.from] at observed
      rcases observed with ⟨rfl,rfl,rfl⟩
      exact bound
    · cases subtracted : ((middle.len - UScalar.cast .Usize value) : Result Usize) with
      | fail error => simp [subtracted] at observed
      | div => simp [subtracted] at observed
      | ok limit =>
        simp only [subtracted,bind_tc_ok] at observed
        exact (actual_loop_bound mi fields ctx limit state middle (status,next,after) observed).trans bound

/-- Full actual generic submessage merger, all wire kinds/recursion counts and
all ordinary success/error returns. No child-limit compliance premise. -/
theorem message_merge_bound {M : Type} (mi : prost.message.Message M) (fields : FieldBound mi)
    (wire : prost.encoding.wire_type.WireType) (ctx : prost.encoding.DecodeContext)
    (state next : M) (before after : Slice U8) (status : core.result.Result Unit prost.error.DecodeError)
    (observed : prost.encoding.message.merge mi sliceBuf wire state before ctx = .ok (status,next,after)) :
    after.length ≤ before.length := by
  unfold prost.encoding.message.merge at observed
  cases checked : prost.encoding.wire_type.check_wire_type .LengthDelimited wire with
  | fail error => simp [checked] at observed
  | div => simp [checked] at observed
  | ok result =>
    cases result with
    | Err error =>
      simp [checked,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from] at observed
      rcases observed with ⟨rfl,rfl,rfl⟩
      exact Nat.le_refl _
    | Ok unit =>
      simp only [checked,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch] at observed
      cases reached : prost.encoding.DecodeContext.limit_reached ctx with
      | fail error => simp [reached] at observed
      | div => simp [reached] at observed
      | ok result =>
        cases result with
        | Err error =>
          simp [reached,core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from] at observed
          rcases observed with ⟨rfl,rfl,rfl⟩
          exact Nat.le_refl _
        | Ok unit =>
          simp only [reached,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch] at observed
          cases entered : prost.encoding.DecodeContext.enter_recursion ctx with
          | fail error => simp [entered] at observed
          | div => simp [entered] at observed
          | ok inner =>
            simp only [entered,bind_tc_ok] at observed
            exact merge_loop_bound mi fields inner state next before after status observed
#print axioms merge_loop_bound
#print axioms message_merge_bound
end ChatResponseReference.SubmessageGenericV1
