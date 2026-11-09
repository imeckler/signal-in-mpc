import ChatResponseReferenceWork.StreamingV1.NativeMessageHeaderState
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipSlice

theorem copied_string_bytes (after : Slice U8) (native : U64) :
    (copiedString after native).val.map (fun byte => byte.bv) =
      contents (ActualResponseBytesV1.ContentModel.take after (UScalar.cast .Usize native).val) := rfl

theorem copied_string_length (after : Slice U8) (native : U64) (fits : native.val ≤ after.length) :
    ((copiedString after native).val.map (fun byte => byte.bv)).length = native.val := by
  rw [copied_string_bytes]
  simpa only [contents,List.length_map] using copied_body_length after native fits

#print axioms copied_string_bytes
#print axioms copied_string_length
end ChatResponseReference.StreamingV1
