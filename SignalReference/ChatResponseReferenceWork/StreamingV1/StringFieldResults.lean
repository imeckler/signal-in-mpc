import ChatResponseReferenceWork.StreamingV1.StringDispatch
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open ActualInnerResponseV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

def copiedString (after : Slice U8) (native : U64) : ActualInnerResponseV1.String :=
  LibSignalReference.Candidate.ProstVecAdapter.fromSlice (ChatResponseReference.ContiguousPut.view ⟨after,UScalar.cast .Usize native⟩)

theorem message_field_utf_success (source : InnerResponseV1.Message) (after : Slice U8) (native : U64)
    (fits : native.val ≤ after.length)
    (utf : Utf8.accepts ((copiedString after native).val.map (fun (byte : U8) => byte.bv)) = true) :
    messageFieldDecoded source (.Ok native) after =
      .ok (.Ok (),{source with message := some (copiedString after native)},LibSignalReference.Candidate.ProstBytesBuf.drop after native.val) := by
  unfold copiedString at utf ⊢
  simp only [messageFieldDecoded,StringContentV3.bytesResult,if_pos fits,StringContentV3.stringResult,utf,if_true,
    InnerResponseV1.strongStringResult,InnerResponseV1.stamp,bind_tc_ok]

/-- Invalid UTF8 always clears the String, even replacing an existing value;
the exact error and subsequent diagnostic push effects are retained. -/
theorem message_field_utf_failure (source : InnerResponseV1.Message) (after : Slice U8) (native : U64)
    (fits : native.val ≤ after.length)
    (utf : Utf8.accepts ((copiedString after native).val.map (fun (byte : U8) => byte.bv)) = false) :
    messageFieldDecoded source (.Ok native) after =
      (do let observed ← InnerResponseV1.stamp diagnosticFrame2
            (.Err (fromStringError (StringContentV3.decodeError .InvalidString)))
          .ok (observed,{source with message := some (alloc.vec.Vec.new U8)},LibSignalReference.Candidate.ProstBytesBuf.drop after native.val)) := by
  unfold copiedString at utf
  simp only [messageFieldDecoded,StringContentV3.bytesResult,if_pos fits,StringContentV3.stringResult,utf,
    Bool.false_eq_true,if_false,InnerResponseV1.strongStringResult]

#print axioms message_field_utf_success
#print axioms message_field_utf_failure
end ChatResponseReference.StreamingV1
