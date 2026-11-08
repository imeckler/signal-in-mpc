import ChatResponseReferenceWork.BytesContentV1.Replayed.Types
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.SchemaV1.Diagnostic
open ActualResponseBytesV1
abbrev Error := prost.error.DecodeError
abbrev Kind := prost.error.DecodeErrorKind
abbrev Frame := Str × Str
/-- Explicit content model of the inspected native push body. The actual static
reference extraction bridge remains open. The Vec operation is executed, so its
allocation/capacity failure is retained before any observation is applied. -/
def push (error : Error) (frame : Frame) : Result Error := do
  let stack ← alloc.vec.Vec.push error.inner.stack frame
  .ok ⟨⟨error.inner.description,stack⟩⟩

/-- Exact all-outcomes projection: neither failure nor divergence is turned into
an ordinary decoder rejection by hiding diagnostics. -/
theorem push_kind_all_outcomes (error : Error) (frame : Frame) :
    (do let next ← push error frame; .ok next.inner.description) =
      (do let _ ← alloc.vec.Vec.push error.inner.stack frame; .ok error.inner.description) := by
  unfold push
  cases alloc.vec.Vec.push error.inner.stack frame <;> rfl

theorem push_bounded (error : Error) (frame : Frame)
    (bound : error.inner.stack.val.length < Usize.max) :
    ∃ next, push error frame = .ok next ∧
      next.inner.description = error.inner.description ∧
      next.inner.stack.val = error.inner.stack.val ++ [frame] := by
  obtain ⟨stack,run,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec error.inner.stack frame bound)
  exact ⟨⟨⟨error.inner.description,stack⟩⟩,by simp only [push,run,bind_tc_ok],rfl,contents⟩

/-- Nested callbacks append inner then outer. This records mutation order before
projecting diagnostic contents; no commutation or unconditional totality claim. -/
theorem push_two_order (error : Error) (inner outer : Frame)
    (bound : error.inner.stack.val.length+2 ≤ Usize.max) :
    ∃ next, (do let middle ← push error inner; push middle outer) = .ok next ∧
      next.inner.description = error.inner.description ∧
      next.inner.stack.val = error.inner.stack.val ++ [inner,outer] := by
  obtain ⟨middle,first,kind1,contents1⟩ := push_bounded error inner (by omega)
  have secondBound : middle.inner.stack.val.length < Usize.max := by
    rw [contents1,List.length_append,List.length_singleton]
    omega
  obtain ⟨next,second,kind2,contents2⟩ := push_bounded middle outer secondBound
  refine ⟨next,by simp only [first,bind_tc_ok,second],kind2.trans kind1,?_⟩
  rw [contents2,contents1,List.append_assoc]
  rfl

/-- Functional owned-decoder observation. It preserves the complete failure or
success result and cursor, and on Err retains the exact constructor/parameters.
Only the diagnostic stack is hidden. Log text is outside this observation. -/
def observe {Value Record Cursor : Type}
    (result : Result (core.result.Result Value Error × Record × Cursor)) :
    Result (core.result.Result Value Kind × Cursor) := do
  let (decoded,_,cursor) ← result
  match decoded with
  | .Ok value => .ok (.Ok value,cursor)
  | .Err error => .ok (.Err error.inner.description,cursor)

/-- Execute the callback first. Failure/divergence/allocation effects and the
already-computed cursor are retained; successful push alone hides its stack. -/
theorem observe_error_push {Value Record Cursor : Type} (record : Record)
    (cursor : Cursor) (error : Error) (frame : Frame) :
    observe (do let next ← push error frame
                .ok ((core.result.Result.Err next : core.result.Result Value Error),record,cursor)) =
      (do let _ ← alloc.vec.Vec.push error.inner.stack frame
          .ok ((core.result.Result.Err error.inner.description : core.result.Result Value Kind),cursor)) := by
  unfold observe push
  cases alloc.vec.Vec.push error.inner.stack frame <;> rfl

/-- The inspected ChatConnection caller warns and continues on DataError. This
is the request-state/event observation, excluding the actual warning log text.
It is intentionally separate from Mux's stricter abort policy. -/
def ignoredDataError (pending : State) (_error : Error) : State × Option Event := (pending,none)
theorem caller_diagnostics_unobservable (pending : State) (first second : Error) :
    ignoredDataError (Event:=Event) pending first = ignoredDataError pending second := rfl
#print axioms push_kind_all_outcomes
#print axioms push_bounded
#print axioms push_two_order
#print axioms observe_error_push
#print axioms caller_diagnostics_unobservable
end ChatResponseReference.SchemaV1.Diagnostic
