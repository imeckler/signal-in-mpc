import ChatResponseReferenceWork.OuterEnvelopeV1.FieldReference
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.OuterEnvelopeV1
open ActualOuterEnvelopeV1
/-- Same actual optional-field normal form, polymorphic in the containing record. -/
def optional {S T B : Type} (old : Option T) (defaults : Result T)
    (run : T → Result (core.result.Result Unit Error × T × B))
    (set : T → S) (frame : Str × Str) : Result (core.result.Result Unit Error × S × B) := do
  let initial ← match old with | some value => .ok value | none => defaults
  let (status,value,after) ← run initial
  let result ← stamp frame status
  .ok (result,set value,after)

theorem optional_consumption {S T : Type} (old : Option T) (defaults : Result T)
    (run : T → Result (core.result.Result Unit Error × T × Slice U8))
    (set : T → S) (frame : Str × Str) (before after : Slice U8)
    (status : core.result.Result Unit Error) (next : S)
    (primitive : ∀ initial result value suffix, run initial = .ok (result,value,suffix) → suffix.length ≤ before.length)
    (observed : optional old defaults run set frame = .ok (status,next,after)) :
    after.length ≤ before.length := by
  have callback (initial : T)
      (observed : (do
        let (result,value,suffix) ← run initial
        let stamped ← stamp frame result
        .ok (stamped,set value,suffix)) = .ok (status,next,after)) :
      after.length ≤ before.length := by
    cases decoded : run initial with
    | fail error => simp [decoded] at observed
    | div => simp [decoded] at observed
    | ok output =>
      rcases output with ⟨result,value,suffix⟩
      have bound := primitive initial result value suffix decoded
      simp only [decoded,bind_tc_ok] at observed
      cases stamped : stamp frame result with
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
#print axioms optional_consumption
end ChatResponseReference.OuterEnvelopeV1
