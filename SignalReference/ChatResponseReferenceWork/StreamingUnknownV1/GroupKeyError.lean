import ChatResponseReferenceWork.StreamingUnknownV1.GroupLoopReady
import ChatResponseReferenceWork.StreamingV1.AnyKeyError
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstSkip

/-- Actual malformed group key preserves its native error/suffix and exits the
real group loop; Core rejects all malformed classes at any supported depth. -/
theorem actual_group_key_error (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (parent count : U32) (parents : List U32) (budget remaining : Nat)
    (error : LoopSupportSkip.error.DecodeError)
    (ready : GroupLoopReady state before budget remaining parents count)
    (actual : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Err error,after)) :
    LoopSupportSkip.encoding.skip_field_loop.body sliceBuf parent ⟨count⟩ before = .ok (.done (.Err error,after)) ∧
    LoopSupportSkip.encoding.skip_field_loop sliceBuf parent before ⟨count⟩ = .ok (.Err error,after) ∧
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  have step := group_key_error before after parent ⟨count⟩ error actual
  exact ⟨step,group_loop_done _ _ _ _ step,any_native_key_error_reject state before after error
    (by have := ready.common.positive; have := ready.common.physical; omega) ready.modes ready.common.positions ready.common.value actual⟩

#print axioms actual_group_key_error
end ChatResponseReference.StreamingUnknownV1
