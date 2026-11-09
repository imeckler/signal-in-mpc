import ChatResponseReferenceWork.InnerScanV1.ContentConsumption
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.InnerScanV1
open ActualInnerResponseV1

theorem append_suffix (old : alloc.vec.Vec ActualInnerResponseV1.String)
    (input : core.result.Result Unit ActualStringContentV3.error.DecodeError × ActualInnerResponseV1.String × Slice U8)
    (output : core.result.Result Unit ActualStringContentV3.error.DecodeError × alloc.vec.Vec ActualInnerResponseV1.String × Slice U8)
    (run : RepeatedStringV1.appendResult old input = .ok output) :
    output.2.2 = input.2.2 := by
  rcases input with ⟨status,value,suffix⟩
  cases status with
  | Err error => cases run; rfl
  | Ok unit =>
    simp only [RepeatedStringV1.appendResult] at run
    cases pushed : alloc.vec.Vec.push old value with
    | fail error => simp [pushed] at run
    | div => simp [pushed] at run
    | ok values => simp [pushed] at run; cases run; rfl

/-- A successful repeated-header callback cannot change the primitive suffix;
failed allocation remains an outer effect, rather than a synthetic Err. -/
theorem header_consumption (old value : alloc.vec.Vec ActualInnerResponseV1.String)
    (before after : Slice U8) (ctx : prost.encoding.DecodeContext)
    (status : core.result.Result Unit prost.error.DecodeError)
    (observed : prost.encoding.string.merge_repeated InnerResponseV1.sliceBuf .LengthDelimited old before ctx =
      .ok (status,value,after)) : after.length ≤ before.length := by
  obtain ⟨decoded,middle,hpost,error,run⟩ := InnerResponseV1.headers_full_reference old before ctx
  let body := StringContentV3.stringResult (StringContentV3.bytesResult (alloc.vec.Vec.new U8) decoded middle)
  have strongSuffix : (InnerResponseV1.strongStringResult body).2.2 = body.2.2 := by
    cases body with
    | mk status rest => cases status <;> rfl
  have bound : body.2.2.length ≤ before.length := by
    rw [← strongSuffix]
    exact (string_result_bound (alloc.vec.Vec.new U8) decoded middle).trans
      (decoded_suffix_bound before middle decoded hpost error)
  rw [run] at observed
  change (do let result ← RepeatedStringV1.appendResult old body
             .ok (InnerResponseV1.mapRepeatedResult result)) = .ok (status,value,after) at observed
  cases appended : RepeatedStringV1.appendResult old body with
  | fail error => simp [appended] at observed
  | div => simp [appended] at observed
  | ok output =>
    have suffix := append_suffix old body output appended
    rcases output with ⟨result,headers,remaining⟩
    cases result <;> simp [appended,InnerResponseV1.mapRepeatedResult] at observed
    all_goals rcases observed with ⟨_,_,rfl⟩; change remaining = body.2.2 at suffix; rw [suffix]; exact bound
theorem header_all_wire_consumption (old value : alloc.vec.Vec ActualInnerResponseV1.String)
    (wire : prost.encoding.wire_type.WireType) (before after : Slice U8)
    (ctx : prost.encoding.DecodeContext) (status : core.result.Result Unit prost.error.DecodeError)
    (observed : prost.encoding.string.merge_repeated InnerResponseV1.sliceBuf wire old before ctx =
      .ok (status,value,after)) : after.length ≤ before.length := by
  by_cases correct : wire = .LengthDelimited
  · subst wire; exact header_consumption old value before after ctx status observed
  · have wrong : prost.encoding.string.merge_repeated InnerResponseV1.sliceBuf wire old before ctx =
        .ok (.Err (fromStringError (StringContentV3.decodeError (.UnexpectedWireType (toStringWire wire) .LengthDelimited))),old,before) := by
      cases wire <;> first | exact False.elim (correct rfl) | rfl
    rw [wrong] at observed
    cases observed
    exact Nat.le_refl _
#print axioms header_all_wire_consumption
#print axioms append_suffix
#print axioms header_consumption
end ChatResponseReference.InnerScanV1
