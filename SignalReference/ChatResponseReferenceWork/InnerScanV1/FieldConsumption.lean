import ChatResponseReferenceWork.InnerScanV1.HeaderConsumption
import ChatResponseReferenceWork.InnerResponseV1.SkipReference
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.InnerScanV1
open ActualInnerResponseV1

theorem optional_consumption {T : Type} (old : Option T) (defaults : Result T)
    (run : T → Result (core.result.Result Unit prost.error.DecodeError × T × Slice U8))
    (set : T → Message) (frame : InnerResponseV1.Frame) (before after : Slice U8)
    (status : core.result.Result Unit prost.error.DecodeError) (next : Message)
    (primitive : ∀ initial result value suffix, run initial = .ok (result,value,suffix) → suffix.length ≤ before.length)
    (observed : InnerResponseV1.optionalField old defaults run set frame = .ok (status,next,after)) :
    after.length ≤ before.length := by
  have callback (initial : T)
      (observed : (do
        let (result,value,suffix) ← run initial
        let stamped ← InnerResponseV1.stamp frame result
        .ok (stamped,set value,suffix)) = .ok (status,next,after)) :
      after.length ≤ before.length := by
    cases decoded : run initial with
    | fail error => simp [decoded] at observed
    | div => simp [decoded] at observed
    | ok output =>
      rcases output with ⟨result,value,suffix⟩
      have bound := primitive initial result value suffix decoded
      simp only [decoded,bind_tc_ok] at observed
      cases stamped : InnerResponseV1.stamp frame result with
      | fail error => simp [stamped] at observed
      | div => simp [stamped] at observed
      | ok result => simp [stamped] at observed; rcases observed with ⟨_,_,rfl⟩; exact bound
  cases old with
  | some initial => exact callback initial observed
  | none =>
    cases defaults with
    | fail error => cases observed
    | div => cases observed
    | ok initial => exact callback initial observed
theorem bound_of_reference {T E : Type} {source : Result (core.result.Result Unit E × T × Slice U8)}
    {before after : Slice U8} {status : core.result.Result Unit E} {value : T}
    (reference : ∃ result value suffix, source = .ok (result,value,suffix) ∧ suffix.length ≤ before.length)
    (observed : source = .ok (status,value,after)) : after.length ≤ before.length := by
  obtain ⟨result,initial,suffix,run,bound⟩ := reference
  rw [run] at observed
  cases observed
  exact bound

theorem field_consumption (state next : Message) (tag : U32)
    (wire : prost.encoding.wire_type.WireType) (before after : Slice U8)
    (ctx : prost.encoding.DecodeContext) (status : core.result.Result Unit prost.error.DecodeError)
    (observed : InnerResponseV1.fieldSpec InnerResponseV1.sliceBuf state tag wire before ctx =
      .ok (status,next,after)) : after.length ≤ before.length := by
  unfold InnerResponseV1.fieldSpec at observed
  split at observed
  · apply optional_consumption (primitive := ?_) (observed := observed)
    intro initial result value suffix run
    exact bound_of_reference (scalar_consumption initial 0#u32 wire before ctx).2 run
  · apply optional_consumption (primitive := ?_) (observed := observed)
    intro initial result value suffix run
    exact bound_of_reference (scalar_consumption 0#u64 initial wire before ctx).1 run
  · apply optional_consumption (primitive := ?_) (observed := observed)
    intro initial result value suffix run
    exact bound_of_reference (string_all_wire_consumption initial wire before ctx) run
  · apply optional_consumption (primitive := ?_) (observed := observed)
    intro initial result value suffix run
    exact bound_of_reference (bytes_consumption initial wire before ctx) run
  · apply optional_consumption (old := some state.headers) (defaults := .ok state.headers)
      (run := fun initial => prost.encoding.string.merge_repeated InnerResponseV1.sliceBuf wire initial before ctx)
      (set := fun value => {state with headers := value}) (frame := diagnosticFrame4)
      (primitive := ?_) (observed := observed)
    intro initial result value suffix run
    exact header_all_wire_consumption initial value wire before suffix ctx result run
  · obtain ⟨result,semantics,run,bound⟩ := InnerResponseV1.skip_full_reference wire tag before ctx
    rw [run] at observed
    rcases result with ⟨result,suffix⟩
    cases result <;> cases observed <;> exact bound
#print axioms field_consumption
#print axioms optional_consumption
end ChatResponseReference.InnerScanV1
