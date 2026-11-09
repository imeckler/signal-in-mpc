import ChatResponseReferenceWork.InnerScanV1.Consumption
import ChatResponseReferenceWork.InnerResponseV1.BytesReference
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.InnerScanV1
open ActualInnerResponseV1

theorem string_all_wire_consumption (old : ActualInnerResponseV1.String)
    (wire : prost.encoding.wire_type.WireType) (before : Slice U8) (ctx : prost.encoding.DecodeContext) :
    ∃ result value after,
      prost.encoding.string.merge InnerResponseV1.sliceBuf wire old before ctx = .ok (result,value,after) ∧
      after.length ≤ before.length := by
  cases wire <;> first
    | exact string_consumption old before ctx
    | exact ⟨_,_,_,rfl,Nat.le_refl _⟩

theorem bytes_result_bound (old : bytes.bytes.Bytes)
    (decoded : core.result.Result U64 LoopSupportSkip.error.DecodeError) (after : Slice U8) :
    (BytesContentV1.bytesResult old decoded after).2.2.length ≤ after.length := by
  cases decoded with
  | Err error => exact Nat.le_refl _
  | Ok value =>
    simp only [BytesContentV1.bytesResult]
    split
    · change (LibSignalReference.Candidate.ProstBytesBuf.drop after value.val).length ≤ after.length
      simp only [LibSignalReference.Candidate.ProstBytesBuf.drop,Slice.length,List.length_drop]
      omega
    · exact Nat.le_refl _

theorem bytes_consumption (old : bytes.bytes.Bytes) (wire : prost.encoding.wire_type.WireType)
    (before : Slice U8) (ctx : prost.encoding.DecodeContext) :
    ∃ result value after,
      prost.encoding.bytes.merge bytes.bytes.Bytes.Insts.ProstEncodingBytesAdapter
        InnerResponseV1.byteSlice wire old before ctx = .ok (result,value,after) ∧
      after.length ≤ before.length := by
  have lengthCase : ∃ result value after,
      prost.encoding.bytes.merge bytes.bytes.Bytes.Insts.ProstEncodingBytesAdapter
        InnerResponseV1.byteSlice .LengthDelimited old before ctx = .ok (result,value,after) ∧
      after.length ≤ before.length := by
    obtain ⟨decoded,after,hpost,error,run⟩ := InnerResponseV1.bytes_full_reference old before ctx
    exact ⟨_,_,_,run,(bytes_result_bound old decoded after).trans (decoded_suffix_bound before after decoded hpost error)⟩
  cases wire <;> first
    | exact lengthCase
    | exact ⟨_,_,_,rfl,Nat.le_refl _⟩
#print axioms string_all_wire_consumption
#print axioms bytes_consumption
end ChatResponseReference.InnerScanV1
