import ChatResponseReferenceWork.InnerResponseV1.StringBridge
import ChatResponseReferenceWork.InnerResponseV1.ScalarReference
import ChatResponseReferenceWork.StringContentV3.FullStringReference
import ChatResponseReferenceWork.RepeatedStringV1.Reference
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.InnerResponseV1
open ActualInnerResponseV1

theorem string_buffer_exact : stringBuf sliceBuf = ChatResponseReference.StringContentV3.sliceBuf := rfl
theorem repeated_buffer_exact : repeatedBuf sliceBuf = ChatResponseReference.RepeatedStringV1.sliceBuf := rfl

def strongStringResult {B : Type} (result : core.result.Result Unit ActualStringContentV3.error.DecodeError × ActualInnerResponseV1.String × B) :
    core.result.Result Unit prost.error.DecodeError × ActualInnerResponseV1.String × B :=
  match result.1 with
  | .Ok unit => (.Ok unit,result.2.1,result.2.2)
  | .Err error => (.Err (fromStringError error),alloc.vec.Vec.new U8,result.2.2)

theorem string_all_outcomes {B : Type} (inst : bytes.buf.buf_impl.Buf B)
    (wire : prost.encoding.wire_type.WireType) (old : ActualInnerResponseV1.String) (before : B) (ctx : prost.encoding.DecodeContext) :
    prost.encoding.string.merge inst wire old before ctx =
      (do let result ← ActualStringContentV3.encoding.string.merge (stringBuf inst) (toStringWire wire) old before (stringCtx ctx)
          .ok (strongStringResult result)) := by
  unfold prost.encoding.string.merge
  cases run : ActualStringContentV3.encoding.string.merge (stringBuf inst) (toStringWire wire) old before (stringCtx ctx) with
  | fail error => rfl
  | div => rfl
  | ok result =>
    rcases result with ⟨r,value,after⟩
    cases r <;> rfl

/-- Strong field-return state: actual total clear on every String error precedes
its caller's callback; exact constructor/parameters and suffix remain visible. -/
theorem string_full_reference (old : ActualInnerResponseV1.String) (before : Slice U8) (ctx : prost.encoding.DecodeContext) :
    ∃ decoded after,
      LibSignalReference.Candidate.ProstSkipBuf.PrefixPost before decoded after ∧
      LibSignalReference.Candidate.ProstSkipBuf.ErrorPost before decoded after ∧
      prost.encoding.string.merge sliceBuf .LengthDelimited old before ctx =
        .ok (strongStringResult (ChatResponseReference.StringContentV3.stringResult
          (ChatResponseReference.StringContentV3.bytesResult old decoded after))) := by
  obtain ⟨decoded,after,prefixPost,errorPost,run⟩ := ChatResponseReference.StringContentV3.string_full_reference before old (stringCtx ctx)
  refine ⟨decoded,after,prefixPost,errorPost,?_⟩
  rw [string_all_outcomes,string_buffer_exact]
  change (do let result ← ActualStringContentV3.encoding.string.merge ChatResponseReference.StringContentV3.sliceBuf .LengthDelimited old before (stringCtx ctx)
             .ok (strongStringResult result)) = _
  rw [run]
  rfl

def mapRepeatedResult {B : Type}
    (result : core.result.Result Unit ActualStringContentV3.error.DecodeError × alloc.vec.Vec ActualInnerResponseV1.String × B) :
    core.result.Result Unit prost.error.DecodeError × alloc.vec.Vec ActualInnerResponseV1.String × B :=
  match result.1 with
  | .Ok unit => (.Ok unit,result.2.1,result.2.2)
  | .Err error => (.Err (fromStringError error),result.2.1,result.2.2)

theorem map_repeated_all {B : Type}
    (input : Result (core.result.Result Unit ActualStringContentV3.error.DecodeError × alloc.vec.Vec ActualInnerResponseV1.String × B)) :
    (do let (r,value,suffix) ← input
        match r with
        | .Ok unit => .ok ((core.result.Result.Ok unit : core.result.Result Unit prost.error.DecodeError),value,suffix)
        | .Err error => .ok ((core.result.Result.Err (fromStringError error) : core.result.Result Unit prost.error.DecodeError),value,suffix)) =
      (do let result ← input; .ok (mapRepeatedResult result)) := by
  cases input with
  | fail error => rfl
  | div => rfl
  | ok result => rcases result with ⟨r,value,suffix⟩; cases r <;> rfl

/-- Repeated-field allocation failure/divergence is preserved outside the map;
ordinary error retains the old header array with the exact native suffix. -/
theorem headers_full_reference (old : alloc.vec.Vec ActualInnerResponseV1.String) (before : Slice U8) (ctx : prost.encoding.DecodeContext) :
    ∃ decoded after,
      LibSignalReference.Candidate.ProstSkipBuf.PrefixPost before decoded after ∧
      LibSignalReference.Candidate.ProstSkipBuf.ErrorPost before decoded after ∧
      prost.encoding.string.merge_repeated sliceBuf .LengthDelimited old before ctx =
        (do let result ← ChatResponseReference.RepeatedStringV1.appendResult old
              (ChatResponseReference.StringContentV3.stringResult
                (ChatResponseReference.StringContentV3.bytesResult (alloc.vec.Vec.new U8) decoded after))
            .ok (mapRepeatedResult result)) := by
  obtain ⟨decoded,after,prefixPost,errorPost,run⟩ := ChatResponseReference.RepeatedStringV1.repeated_full_reference before old (stringCtx ctx)
  refine ⟨decoded,after,prefixPost,errorPost,?_⟩
  unfold prost.encoding.string.merge_repeated
  rw [repeated_buffer_exact]
  change (do let (r,value,suffix) ← ActualRepeatedStringV1.encoding.string.merge_repeated
               ChatResponseReference.RepeatedStringV1.sliceBuf .LengthDelimited old before (stringCtx ctx)
             match r with
             | .Ok unit => .ok ((core.result.Result.Ok unit : core.result.Result Unit prost.error.DecodeError),value,suffix)
             | .Err error => .ok ((core.result.Result.Err (fromStringError error) : core.result.Result Unit prost.error.DecodeError),value,suffix)) = _
  rw [run]
  exact map_repeated_all _

#print axioms string_buffer_exact
#print axioms string_all_outcomes
#print axioms string_full_reference
#print axioms headers_full_reference
end ChatResponseReference.InnerResponseV1
