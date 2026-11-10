import ChatResponseReferenceWork.StreamingUnknownV1.GroupOutcome
import ChatResponseReferenceWork.StreamingUnknownV1.GroupCloseAttempt
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstSkip

/-- The checked actual end-key decision establishes the uniform all-outcome
source group relation, including source success outside the private domain. -/
theorem group_close_outcome (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before after : Slice U8)
    (parent child count : U32) (older : List U32) (budget remaining : Nat)
    (ready : GroupLoopReady state before budget remaining (older++[parent]) count)
    (cache : CacheAgrees outer source state)
    (actual : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Ok (child,.EndGroup),after)) :
    GroupOutcome outer source state before budget remaining older count (groupClose parent child after) := by
  have relation := (actual_group_close_attempt_all outer source state before after parent child count older budget remaining ready cache actual).2.2
  by_cases same : child = parent
  · subst child
    simpa only [GroupOutcome,groupClose,if_pos rfl,if_true,GroupCompatibleEnd,GroupReturnedFrame] using relation
  · simpa only [GroupOutcome,groupClose,if_neg same,if_false] using relation

#print axioms group_close_outcome
end ChatResponseReference.StreamingUnknownV1
