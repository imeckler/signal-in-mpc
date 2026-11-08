import ChatResponseReferenceWork.GeneratedStatus.Funs
namespace ChatResponseReference.Status
open Aeneas Aeneas.Std
open ActualChatResponseStatus

/-- Exact extracted HTTP constructor, including rejection. The niche model
preserves scalar contents and checks nonzero; layout is not observed. -/
theorem from_u16_reference (value : U16) :
    http.status.StatusCode.from_u16 value =
      .ok (if 100#u16 ≤ value ∧ value ≤ 999#u16 then
        .Ok value else .Err ⟨()⟩) := by
  simp only [http.status.StatusCode.from_u16, core.num.nonzero.NonZero.new,
    http.status.InvalidStatusCode.new]
  split <;> rename_i lower
  · split <;> rename_i upper
    · have nz : value ≠ 0#u16 := by scalar_tac
      simp [nz, lower, upper]
    · simp [lower, upper]
  · simp [lower]

theorem as_u16_reference (value : U16) :
    http.status.StatusCode.as_u16 value = .ok value := rfl

theorem is_success_reference (value : U16) :
    http.status.StatusCode.is_success value =
      .ok (decide (200#u16 ≤ value ∧ value < 300#u16)) := by
  simp [http.status.StatusCode.is_success, core.num.nonzero.NonZero.get,
    core.ops.range.Range.contains, core.cmp.PartialOrdU16,
    core.cmp.impls.PartialOrdU16.le, core.cmp.impls.PartialOrdU16.lt]
  split <;> simp_all

/-- Actual checked u32 conversion followed by actual HTTP validation. Both
conversion and HTTP failures remain errors; this is not success-only. -/
theorem checked_status_reference (raw : U32) :
    checked_status raw = .ok (
      if raw.val ≤ UScalar.max .U16 then
        let value := UScalar.cast .U16 raw
        if 100#u16 ≤ value ∧ value ≤ 999#u16 then
          .Ok (value, decide (200#u16 ≤ value ∧ value < 300#u16))
        else .Err ()
      else .Err ()) := by
  simp only [checked_status, U16.Insts.CoreConvertTryFromU32TryFromIntError.try_from,
    core.num.tryFromUScalar]
  split <;> simp [core.result.Result.map_err,
    checked_status.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorTuple,
    checked_status.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorTuple.call_once,
    checked_status.closure_1.Insts.CoreOpsFunctionFnOnceTupleInvalidStatusCodeTuple,
    checked_status.closure_1.Insts.CoreOpsFunctionFnOnceTupleInvalidStatusCodeTuple.call_once,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame, from_u16_reference, as_u16_reference, is_success_reference]
  split <;> split_ifs at * <;> simp_all
  all_goals subst_vars; rfl

#print axioms checked_status_reference
#print axioms from_u16_reference
#print axioms as_u16_reference
#print axioms is_success_reference
end ChatResponseReference.Status
