import ChatResponseReferenceWork.StreamingV1.MessageByteValidity
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.Utf8

theorem run_dead (bytes : List (BitVec 8)) : run .dead bytes = .dead := by
  induction bytes with
  | nil => rfl
  | cons byte rest ih => exact ih

theorem run_append (phase : Phase) (first second : List (BitVec 8)) :
    run phase (first ++ second) = run (run phase first) second := by
  induction first generalizing phase with
  | nil => rfl
  | cons byte rest ih => exact ih _

theorem accepted_next_live (phase : Phase) (byte : BitVec 8) (rest : List (BitVec 8))
    (accepted : run phase (byte::rest) = .ready) : next phase byte ≠ .dead := by
  intro dead
  change run (next phase byte) rest = .ready at accepted
  rw [dead,run_dead] at accepted
  cases accepted

#print axioms run_dead
#print axioms run_append
#print axioms accepted_next_live
end ChatResponseReference.Utf8
