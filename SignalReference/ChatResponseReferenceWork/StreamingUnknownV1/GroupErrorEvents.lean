import ChatResponseReferenceWork.StreamingUnknownV1.GroupEventPrimitives
import ChatResponseReferenceWork.StreamingV1.RejectionClosure
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1

/-- Sticky rejection suppresses exported event masks for arbitrary remaining
capacity bytes; payload bytes themselves remain present in the trace. -/
theorem rejected_events_zero (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (byte : BitVec 8) (invalid : state.valid = 0) :
    let event := TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte
    event.bodyData = 0 ∧ event.bodyReset = 0 ∧ event.headerData = 0 := by
  have next := step_invalid_sticky state byte invalid
  have zeroAnd (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  have validEq : (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.valid = 0 := next
  refine ⟨?_,?_,?_⟩
  all_goals
    change ByteAuth.concrete.and (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.valid _ = 0
    rw [validEq]
    exact zeroAnd _

theorem rejected_trace_zero (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (bytes : List (BitVec 8)) (invalid : state.valid = 0) :
    bodyTrace state bytes = bytes.map (fun byte => (0,0,0,byte)) := by
  induction bytes generalizing state with
  | nil => rfl
  | cons byte rest ih =>
    have event := rejected_events_zero state byte invalid
    change (_,_,_,byte)::bodyTrace _ rest = (0,0,0,byte)::rest.map _
    rw [event.1,event.2.1,event.2.2,ih _ (step_invalid_sticky state byte invalid)]

#print axioms rejected_events_zero
#print axioms rejected_trace_zero
end ChatResponseReference.StreamingUnknownV1
