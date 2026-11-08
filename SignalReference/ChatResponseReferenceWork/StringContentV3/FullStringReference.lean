import ChatResponseReferenceWork.StringContentV3.BytesReference
import ChatResponseReferenceWork.StringContentV3.ControlReference
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.StringContentV3
open ActualStringContentV3

def stringResult (body : MergeResult) : MergeResult :=
  match body.1 with
  | .Err error => (.Err error,body.2.1,body.2.2)
  | .Ok _ => if Utf8.accepts (body.2.1.val.map (fun b => b.bv)) then
      (.Ok (),body.2.1,body.2.2)
    else (.Err (decodeError .InvalidString),body.2.1,body.2.2)

theorem string_from_decode (before after : Slice U8) (old : Value)
    (decoded : core.result.Result U64 LoopSupportSkip.error.DecodeError) (ctx : encoding.DecodeContext)
    (hd : LoopSupportSkip.encoding.varint.decode_varint LibSignalReference.Candidate.ProstSkipBuf.sliceBuf before = .ok (decoded,after)) :
    encoding.string.merge sliceBuf .LengthDelimited old before ctx =
      .ok (stringResult (bytesResult old decoded after)) := by
  rw [string_control]
  unfold stringSpec
  rw [bytes_from_decode before after old decoded ctx hd]
  simp only [bind_tc_ok]
  dsimp! only
  unfold stringResult
  cases h : (bytesResult old decoded after).1 with
  | Err error => rfl
  | Ok unit =>
    by_cases valid : Utf8.accepts ((bytesResult old decoded after).2.1.val.map (fun b => b.bv)) = true
    all_goals simp only [valid,if_true,if_false]
    all_goals rfl

theorem string_wire_error (wire : encoding.wire_type.WireType) (old : Value)
    (before : Slice U8) (ctx : encoding.DecodeContext) (hw : wire ≠ .LengthDelimited) :
    encoding.string.merge sliceBuf wire old before ctx =
      .ok (.Err (decodeError (.UnexpectedWireType wire .LengthDelimited)),old,before) := by
  rw [string_control]
  unfold stringSpec
  rw [bytes_wire_error wire old before ctx hw]
  rfl

/-- Actual String merge under explicit executable UTF8/content models, including
malformed prefix, underflow, invalid UTF8 and success. No primitive correctness
or termination premise. This is a byte-content relation; cleanup must be applied
before using a stronger internal state observation on error. -/
theorem string_full_reference (before : Slice U8) (old : Value) (ctx : encoding.DecodeContext) :
    ∃ decoded after,
      LibSignalReference.Candidate.ProstSkipBuf.PrefixPost before decoded after ∧
      LibSignalReference.Candidate.ProstSkipBuf.ErrorPost before decoded after ∧
      encoding.string.merge sliceBuf .LengthDelimited old before ctx =
        .ok (stringResult (bytesResult old decoded after)) := by
  obtain ⟨decoded,after,hd,hp,he⟩ := LibSignalReference.Candidate.ProstSkipBuf.decode_full_reference before
  exact ⟨decoded,after,hp,he,string_from_decode before after old decoded ctx hd⟩

/-- Execute total cleanup after an actual error. Exact error and suffix remain;
only the error-local field content is hidden at owned decode. -/
theorem string_owned_cleanup (before : Slice U8) (old : Value) (ctx : encoding.DecodeContext) :
    (do let result ← encoding.string.merge sliceBuf .LengthDelimited old before ctx
        .ok (observe (cleanup result))) =
      (do let result ← encoding.string.merge sliceBuf .LengthDelimited old before ctx
          .ok (observe result)) := by
  simp only [cleanup_unobservable]
#print axioms string_wire_error
#print axioms string_full_reference
#print axioms string_owned_cleanup
end ChatResponseReference.StringContentV3
