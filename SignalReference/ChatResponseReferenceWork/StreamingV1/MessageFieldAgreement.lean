import ChatResponseReferenceWork.StreamingV1.NativeMessageFieldValidity
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open ActualInnerResponseV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

def messageFieldOutcome (source : InnerResponseV1.Message) (after : Slice U8) (native : U64) :=
  if Utf8.accepts ((copiedString after native).val.map (fun byte => byte.bv)) then
    .ok (.Ok (),{source with message := some (copiedString after native)},LibSignalReference.Candidate.ProstBytesBuf.drop after native.val)
  else
    do let observed ← InnerResponseV1.stamp diagnosticFrame2
         (.Err (fromStringError (StringContentV3.decodeError .InvalidString)))
       Result.ok (observed,{source with message := some (alloc.vec.Vec.new U8)},LibSignalReference.Candidate.ProstBytesBuf.drop after native.val)

/-- Generated actual String merger agrees with native-derived complete numeric
UTF validity on every copied payload. Invalid UTF retains source clear/diagnostic
Result effects and exact suffix; no supplied post-header or UTF-success premise. -/
theorem actual_message_field_agreement (source : InnerResponseV1.Message)
    (ctx : ActualInnerResponseV1.prost.encoding.DecodeContext) (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (native : U64) (budget remaining : Nat)
    (budgetBound : budget ≤ 4096) (remainingBound : remaining ≤ 4096)
    (budgetEnough : before.length ≤ budget) (physical : remaining ≤ before.length)
    (payloadPhysical : native.val ≤ after.length)
    (childFits : native.val + (before.length-after.length) ≤ remaining)
    (modes : state.modes = lane 2) (positions : state.positions = oneHot 0)
    (utfShape : state.utf.length = 8) (value : state.value = 0) (kinds : state.kinds = [0,0,255,0])
    (valid : state.valid = 255) (seen : state.seen = 255) (finished : state.finished = 0)
    (inner : state.inner = 255) (depth : state.depth = 0)
    (budgetCounter : state.budget = BitVec.ofNat 64 budget)
    (childCounter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (sourceSuccess : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    merge_response InnerResponseV1.sliceBuf source (3#u32) .LengthDelimited before ctx = messageFieldOutcome source after native ∧
    ∃ consumed,
      contents before = consumed ++ contents (LibSignalReference.Candidate.ProstBytesBuf.drop after native.val) ∧
      (feed state consumed).valid = if Utf8.accepts ((copiedString after native).val.map (fun byte => byte.bv)) then 255 else 0 := by
  refine ⟨?_,native_message_field_validity state before after native budget remaining budgetBound remainingBound budgetEnough physical payloadPhysical childFits
    modes positions utfShape value kinds valid seen finished inner depth budgetCounter childCounter sourceSuccess⟩
  rw [actual_message_field_decoded source before after ctx (.Ok native) sourceSuccess]
  unfold messageFieldOutcome
  by_cases accepted : Utf8.accepts ((copiedString after native).val.map (fun byte => byte.bv)) = true
  · rw [if_pos accepted]
    exact message_field_utf_success source after native payloadPhysical accepted
  · rw [if_neg accepted]
    exact message_field_utf_failure source after native payloadPhysical (Bool.eq_false_iff.mpr accepted)

#print axioms actual_message_field_agreement
end ChatResponseReference.StreamingV1
