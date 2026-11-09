import ChatResponseReferenceWork.StreamingUnknownV1.FixedOverrun
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- Exhaustive actual fixed32/fixed64 unknown-field attempt after its real key.
No primitive result, physical fit or private child fit is supplied as a premise. -/
theorem actual_unknown_fixed_attempt_all (outer : ResponseData) (source : InnerResponseV1.Message) (tag : U32)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle : Slice U8)
    (ctx : ActualSubmessageV1.prost.encoding.DecodeContext) (budget remaining : Nat) (wide : Bool)
    (limit : Usize) (limitExact : limit.val = before.length-remaining)
    (unknownTag : 5 < tag.val) (count : ctx.recurse_count ≠ 0#u32)
    (boundary : ChildAtKey state before budget remaining) (cache : CacheAgrees outer source state) (positive : 0 < remaining)
    (keyRun : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before =
      .ok (.Ok (tag,if wide then .SixtyFourBit else .ThirtyTwoBit),middle)) :
    if middle.length < (if wide then 8 else 4) then
      SubmessageV1.callback.call_mut () (source,before,ctx) = .ok (.Err fixedUnderflowError,(),source,middle) ∧
      ActualSubmessageV1.prost.encoding.merge_loop_loop SubmessageV1.callback SubmessageV1.sliceBuf source before ctx () limit =
        .ok (.Err fixedUnderflowError,source,middle) ∧
      (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0
    else if (if wide then 8 else 4) + (before.length-middle.length) ≤ remaining then
      SubmessageV1.callback.call_mut () (source,before,ctx) = .ok (.Ok (),(),source,drop middle (if wide then 8 else 4)) ∧
      SubmessageV1.body ctx limit (source,before,()) = .ok (.cont (source,drop middle (if wide then 8 else 4),())) ∧
      ∃ consumed,
        contents before = consumed ++ contents (drop middle (if wide then 8 else 4)) ∧
        CacheAgrees outer source (feed state consumed) ∧
        ChildAtKey (feed state consumed) (drop middle (if wide then 8 else 4))
          (budget-consumed.length) (remaining-consumed.length)
    else
      SubmessageV1.callback.call_mut () (source,before,ctx) = .ok (.Ok (),(),source,drop middle (if wide then 8 else 4)) ∧
      ActualSubmessageV1.prost.encoding.merge_loop_loop SubmessageV1.callback SubmessageV1.sliceBuf source before ctx () limit =
        .ok (.Err (SubmessageV1.decodeError .DelimitedLengthExceeded),source,drop middle (if wide then 8 else 4)) ∧
      (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  by_cases underflow : middle.length < (if wide then 8 else 4)
  · simp only [if_pos underflow]
    obtain ⟨called,_⟩ := actual_unknown_fixed_underflow_iteration source tag state before middle ctx budget remaining wide
      unknownTag count boundary positive underflow keyRun
    exact ⟨called,actual_unknown_fixed_underflow_loop source tag state before middle ctx budget remaining wide limit limitExact
      unknownTag count boundary positive underflow keyRun⟩
  · simp only [if_neg underflow]
    by_cases fits : (if wide then 8 else 4) + (before.length-middle.length) ≤ remaining
    · simp only [if_pos fits]
      obtain ⟨called,_,_,_,_⟩ := actual_unknown_fixed_iteration outer source tag state before middle ctx budget remaining wide
        unknownTag count boundary cache positive fits keyRun
      exact ⟨called,actual_unknown_fixed_loop_step outer source tag state before middle ctx budget remaining wide limit limitExact
        unknownTag count boundary cache positive fits keyRun⟩
    · simp only [if_neg fits]
      have physical : (if wide then 8 else 4) ≤ middle.length := by omega
      obtain ⟨called,_⟩ := actual_unknown_fixed_overrun_iteration source tag state before middle ctx budget remaining wide
        unknownTag count boundary positive physical fits keyRun
      exact ⟨called,actual_unknown_fixed_overrun_loop source tag state before middle ctx budget remaining wide limit limitExact
        unknownTag count boundary positive physical fits keyRun⟩

#print axioms actual_unknown_fixed_attempt_all
end ChatResponseReference.StreamingUnknownV1
