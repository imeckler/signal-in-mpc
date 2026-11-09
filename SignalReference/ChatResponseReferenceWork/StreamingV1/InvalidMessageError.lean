import ChatResponseReferenceWork.StreamingV1.CopyLoopSteps
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open ActualInnerResponseV1

def invalidMessageError : prost.error.DecodeError :=
  fromStringError (StringContentV3.decodeError .InvalidString)

/-- The fresh actual String InvalidString diagnostic push is executed under its
proved empty-stack bound; failure/divergence is not unconditionally erased. -/
theorem invalid_message_stamp : ∃ error,
    InnerResponseV1.stamp diagnosticFrame2 (.Err invalidMessageError) = .ok (.Err error) ∧
    error.inner.description = invalidMessageError.inner.description ∧
    error.inner.stack.val = [diagnosticFrame2] := by
  obtain ⟨error,run,kind,stack⟩ := SchemaV1.Diagnostic.push_bounded invalidMessageError diagnosticFrame2 (by
    change 0 < Usize.max
    scalar_tac)
  refine ⟨error,?_,kind,?_⟩
  · simp only [InnerResponseV1.stamp,run,bind_tc_ok]
  · exact stack

#print axioms invalid_message_stamp
end ChatResponseReference.StreamingV1
