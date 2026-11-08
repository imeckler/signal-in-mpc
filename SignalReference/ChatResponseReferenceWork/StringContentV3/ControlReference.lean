import ChatResponseReferenceWork.StringContentV3.Generated.Funs
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.StringContentV3
open ActualStringContentV3
abbrev Body := Slice U8
abbrev Value := alloc.vec.Vec U8
abbrev Error := error.DecodeError
abbrev MergeResult := core.result.Result Unit Error × Value × Body
/-- Owned decode exposes the error, not a partially initialized field. Keep the
suffix here too, so this projection does not silently erase input effects. -/
def observe (r : MergeResult) : core.result.Result Value Error × Body :=
  match r.1 with
  | .Ok _ => (.Ok r.2.1,r.2.2)
  | .Err error => (.Err error,r.2.2)
def cleanup (r : MergeResult) : MergeResult :=
  match r.1 with
  | .Ok _ => r
  | .Err error => (.Err error,alloc.vec.Vec.new U8,r.2.2)
theorem cleanup_unobservable (r : MergeResult) : observe (cleanup r) = observe r := by
  rcases r with ⟨r,value,suffix⟩
  cases r <;> rfl

/-- Exact byte-content String control flow, with actual extracted byte merger.
The separate bytes/varint/copier theorem must discharge that remaining call;
UTF8 uses the documented executable grammar, not an assumed validator result. -/
noncomputable def stringSpec (inst : bytes.buf.buf_impl.Buf Body)
    (wire : encoding.wire_type.WireType) (old : Value) (before : Body)
    (ctx : encoding.DecodeContext) : Result MergeResult := do
  let (r,value,suffix) ← encoding.bytes.merge_one_copy.partial_Fun_293 inst wire old before ctx
  match r with
  | .Err error => .ok (.Err error,value,suffix)
  | .Ok _ =>
    if Utf8.accepts (value.val.map (fun b => b.bv)) then .ok (.Ok (),value,suffix)
    else .ok (.Err ⟨⟨.InvalidString,alloc.vec.Vec.new (Str×Str)⟩⟩,value,suffix)

theorem string_control (inst : bytes.buf.buf_impl.Buf Body)
    (wire : encoding.wire_type.WireType) (old : Value) (before : Body)
    (ctx : encoding.DecodeContext) :
    encoding.string.merge inst wire old before ctx = stringSpec inst wire old before ctx := by
  unfold encoding.string.merge alloc.string.String.as_mut_vec stringSpec
  simp only [bind_tc_ok]
  dsimp! only
  cases h : encoding.bytes.merge_one_copy.partial_Fun_293 inst wire old before ctx with
  | fail e => rfl
  | div => rfl
  | ok result =>
    rcases result with ⟨r,value,suffix⟩
    cases r with
    | Err e => rfl
    | Ok unit =>
      cases unit
      unfold core.str.converts.from_utf8
      simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
      dsimp! only
      by_cases valid : Utf8.accepts (value.val.map (fun b => b.bv)) = true
      all_goals simp [valid, alloc.vec.Vec.deref, core.mem.forget.partial_Fun_294,
        core.result.Result.Insts.CoreOpsTry.branch, core.convert.IntoFrom.into,
        error.DecodeError.Insts.CoreConvertFromDecodeErrorKind,
        error.DecodeError.Insts.CoreConvertFromDecodeErrorKind.from]

/-- Cleanup is total in the scoped Vec model, adds no error/panic or suffix
mutation, and cannot alter the owned API observation. Not merge-state equality. -/
theorem actual_clear_total (value : Value) :
    reference_Impl_0.drop value = .ok (alloc.vec.Vec.new U8,id) := rfl
#print axioms cleanup_unobservable
#print axioms string_control
#print axioms actual_clear_total
end ChatResponseReference.StringContentV3
