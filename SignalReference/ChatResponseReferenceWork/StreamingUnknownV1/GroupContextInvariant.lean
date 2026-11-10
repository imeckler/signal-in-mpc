import ChatResponseReferenceWork.StreamingUnknownV1.GroupLoopReady
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1

/-- A live bounded inner frame never has the exhausted source context. -/
theorem group_context_positive (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before : Slice U8) (budget remaining : Nat) (parents : List U32) (count : U32)
    (ready : GroupLoopReady state before budget remaining parents count) : count ≠ 0#u32 := by
  intro zero
  have zeroVal : (0#u32).val = 0 := by decide
  have value : count.val = 0 := (congrArg UScalar.val zero).trans zeroVal
  have := ready.context
  have := ready.bounded
  omega

/-- Restoring the same ancestor stack determines the actual source context;
no independent caller-supplied recursion counter can disagree with it. -/
theorem group_context_unique (state other : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (budget remaining otherBudget otherRemaining : Nat)
    (parents : List U32) (count otherCount : U32)
    (ready : GroupLoopReady state before budget remaining parents count)
    (restored : GroupLoopReady other after otherBudget otherRemaining parents otherCount) : count = otherCount := by
  apply UScalar.eq_of_val_eq
  have := ready.context
  have := restored.context
  omega

#print axioms group_context_positive
#print axioms group_context_unique
end ChatResponseReference.StreamingUnknownV1
