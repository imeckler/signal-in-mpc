import ChatResponseReferenceWork.ParserCircuitCandidateV1.StepStackSafe
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.ParserCircuitCandidateV1

/-- State immediately before terminal byte1 after the key prefix83 80...80
(nine continuation bytes): decoded key2^63+3 is range-invalid but group-shaped. -/
def highKeyState : TlsChatResponse.State (BitVec 8) (BitVec 64) :=
  {TlsChatResponse.initial Word64.concrete ByteAuth.concrete 4096 0 with
    seen := 255,value := 3,positions := List.replicate 9 0 ++ [255]}

/-- Negative regression: actual Core writes tag2^60 to stack scratch on a
malformed key while setting valid0. A universal narrow-stack claim is false. -/
theorem malformed_key_high_tag :
    let next := (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete highKeyState 1).state
    next.valid = 0 ∧ next.stack.head?.getD 0 = BitVec.ofNat 64 (2^60) ∧ ¬NarrowWord (next.stack.head?.getD 0) := by
  unfold NarrowWord
  decide +kernel

#print axioms malformed_key_high_tag
end ChatResponseReference.ParserCircuitCandidateV1
