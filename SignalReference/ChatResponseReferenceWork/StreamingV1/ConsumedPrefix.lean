import ChatResponseReferenceWork.StreamingV1.ScalarData
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1

/-- Two successful field components sharing the same actual native suffix must
refer to the same consumed byte prefix. This joins data and validity witnesses. -/
theorem consumed_prefix_unique (wire suffix first second : List (BitVec 8))
    (one : wire = first ++ suffix) (two : wire = second ++ suffix) : first = second :=
  List.append_cancel_right (one.symm.trans two)

theorem consumed_prefix_length (wire suffix consumed : List (BitVec 8))
    (span : wire = consumed ++ suffix) : consumed.length+suffix.length = wire.length := by
  rw [span,List.length_append]

#print axioms consumed_prefix_unique
end ChatResponseReference.StreamingV1
