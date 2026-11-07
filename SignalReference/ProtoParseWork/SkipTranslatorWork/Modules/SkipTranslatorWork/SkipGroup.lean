import SkipTranslatorWork.SkipLeaf
import SkipTranslatorWork.KeyReference

namespace LibSignalReference.Candidate.ProstSkip
open Aeneas Aeneas.Std LoopSupportSkip
open LibSignalReference.Candidate.ProstSkipBuf
set_option maxHeartbeats 400000

def groupClose (tag inner : U32) (after : Slice U8) :
    core.result.Result Unit error.DecodeError × Slice U8 :=
  if inner = tag then (.Ok (),after)
  else (.Err (decodeError .UnexpectedEndGroupTag),after)

theorem start_group (bytes : Slice U8) (tag count : U32) (hc : count ≠ 0#u32) :
    encoding.skip_field sliceBuf .StartGroup tag bytes ⟨count⟩ =
      encoding.skip_field_loop sliceBuf tag bytes ⟨count⟩ := by
  rw [encoding.skip_field.eq_def]
  simp [encoding.DecodeContext.limit_reached,hc,core.result.Result.Insts.CoreOpsTry.branch]

theorem group_key_error (before after : Slice U8) (tag : U32)
    (ctx : encoding.DecodeContext) (error : error.DecodeError)
    (hkey : encoding.decode_key sliceBuf before = .ok (.Err error,after)) :
    encoding.skip_field_loop.body sliceBuf tag ctx before =
      .ok (.done (.Err error,after)) := by
  rw [encoding.skip_field_loop.body.eq_def]
  simp [hkey,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from]

theorem group_end_after (before after : Slice U8) (tag inner : U32)
    (ctx : encoding.DecodeContext)
    (hkey : encoding.decode_key sliceBuf before = .ok (.Ok (inner,.EndGroup),after)) :
    encoding.skip_field_loop.body sliceBuf tag ctx before =
      .ok (.done (groupClose tag inner after)) := by
  rw [encoding.skip_field_loop.body.eq_def]
  simp only [hkey,bind_tc_ok,uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch]
  by_cases htag : inner = tag
  · subst inner
    simp only [bne_self_eq_false,Bool.false_eq_true,if_false,remaining_spec,lift,bind_tc_ok,
      groupClose,if_true]
    have hzero : ¬(0#u64 > UScalar.cast .U64 after.len) := by scalar_tac
    simp only [if_neg hzero]
    have hz : UScalar.cast .Usize 0#u64 = 0#usize := by
      apply UScalar.eq_of_val_eq
      simp [UScalar.cast_val_eq]
    rw [hz,advance_spec after 0#usize (by scalar_tac)]
    simp only [bind_tc_ok]
    rfl
  · simp [htag,groupClose,decodeError,core.convert.IntoFrom.into,
      error.DecodeError.Insts.CoreConvertFromDecodeErrorKind.from]

def groupChild (result : core.result.Result Unit error.DecodeError) (after : Slice U8) :
    ControlFlow (Slice U8) (core.result.Result Unit error.DecodeError × Slice U8) :=
  match result with
  | .Ok () => .cont after
  | .Err e => .done (.Err e,after)

theorem group_child_after (before middle after : Slice U8) (tag inner : U32)
    (ctx child : encoding.DecodeContext) (kind : encoding.wire_type.WireType)
    (result : core.result.Result Unit error.DecodeError)
    (hkind : kind ≠ .EndGroup)
    (hkey : encoding.decode_key sliceBuf before = .ok (.Ok (inner,kind),middle))
    (hctx : encoding.DecodeContext.enter_recursion ctx = .ok child)
    (hchild : encoding.skip_field sliceBuf kind inner middle child = .ok (result,after)) :
    encoding.skip_field_loop.body sliceBuf tag ctx before = .ok (groupChild result after) := by
  rw [encoding.skip_field_loop.body.eq_def]
  cases kind <;> cases result <;>
    simp_all [core.result.Result.Insts.CoreOpsTry.branch,groupChild,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from]

theorem group_loop_done (before : Slice U8) (tag : U32) (ctx : encoding.DecodeContext)
    (result : core.result.Result Unit error.DecodeError × Slice U8)
    (hbody : encoding.skip_field_loop.body sliceBuf tag ctx before = .ok (.done result)) :
    encoding.skip_field_loop sliceBuf tag before ctx = .ok result := by
  rw [encoding.skip_field_loop.eq_def,loop.eq_1]
  simp only [hbody,bind_tc_ok]

theorem group_loop_cont (before after : Slice U8) (tag : U32) (ctx : encoding.DecodeContext)
    (hbody : encoding.skip_field_loop.body sliceBuf tag ctx before = .ok (.cont after)) :
    encoding.skip_field_loop sliceBuf tag before ctx =
      encoding.skip_field_loop sliceBuf tag after ctx := by
  rw [encoding.skip_field_loop.eq_def,loop.eq_1]
  simp only [hbody,bind_tc_ok]
  rw [encoding.skip_field_loop.eq_def]

/-- A finite composition certificate for actual group-body transitions. Child skips must
already have their own reference theorem; this does not assert whole-parser equivalence. -/
inductive GroupTrace (tag : U32) (ctx : encoding.DecodeContext) :
    Slice U8 → (core.result.Result Unit error.DecodeError × Slice U8) → Prop where
  | done {before result}
      (step : encoding.skip_field_loop.body sliceBuf tag ctx before = .ok (.done result)) :
      GroupTrace tag ctx before result
  | next {before middle result}
      (step : encoding.skip_field_loop.body sliceBuf tag ctx before = .ok (.cont middle))
      (rest : GroupTrace tag ctx middle result) : GroupTrace tag ctx before result

theorem group_trace_reference {before : Slice U8} {tag : U32} {ctx : encoding.DecodeContext}
    {result : core.result.Result Unit error.DecodeError × Slice U8}
    (trace : GroupTrace tag ctx before result) :
    encoding.skip_field_loop sliceBuf tag before ctx = .ok result := by
  induction trace with
  | done step => exact group_loop_done _ _ _ _ step
  | next step _ ih => rw [group_loop_cont _ _ _ _ step]; exact ih

end LibSignalReference.Candidate.ProstSkip
