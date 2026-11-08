import ChatResponseReferenceWork.GeneratedOwnedTransferred.Funs
open Aeneas Aeneas.Std Result
namespace ChatResponseOwnedTransferred
open ActualChatResponseOwned_transferred
/-- Structural owned API observation, including allocator/panic failure in the
outer Result. Parsing itself is the explicit supplied merge operation. -/
theorem decode_normal_form {M B : Type} (mi : prost.message.Message M)
    (di : core.default.Default M) (bi : bytes.buf.buf_impl.Buf B) (buf : B) :
    owned_slice_replay.decode_buffer mi di bi buf = (do
      let initial ← di.default
      let (r, final) ← mi.merge bi initial buf
      match r with
      | .Ok _ => .ok (.Ok final)
      | .Err error => .ok (.Err error)) := by
  unfold owned_slice_replay.decode_buffer
  cases hd : di.default <;> try rfl
  rename_i initial
  simp only [Aeneas.Std.bind_tc_ok]
  cases hm : mi.merge bi initial buf <;> try rfl
  rename_i pair
  rcases pair with ⟨r, final⟩
  simp only [Aeneas.Std.bind_tc_ok]
  cases r <;> rfl
/-- A failed owned decode reveals the exact error and no partially mutated M.
No mutation effect is erased from merge itself. -/
theorem decode_error {M B : Type} (mi : prost.message.Message M)
    (di : core.default.Default M) (bi : bytes.buf.buf_impl.Buf B) (buf : B)
    (initial final : M) (error : ActualChatResponseOwned_transferred.prost.error.DecodeError)
    (hd : di.default = .ok initial)
    (hm : mi.merge bi initial buf = .ok (.Err error, final)) :
    owned_slice_replay.decode_buffer mi di bi buf = .ok (.Err error) := by
  rw [decode_normal_form, hd]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hm]
  rfl
#print axioms decode_normal_form
#print axioms decode_error
end ChatResponseOwnedTransferred
