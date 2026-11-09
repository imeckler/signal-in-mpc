import ChatResponseReferenceWork.InnerScanV1.DriverReference
import ChatResponseReferenceWork.InnerResponseV1.ScalarReference
import ChatResponseReferenceWork.InnerResponseV1.StringReference
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.InnerScanV1
open ActualInnerResponseV1
/-- All wire kinds, both scalar widths, existing values and native decoder
errors. No scalar/varint termination or consumption premise is assumed. -/
theorem scalar_consumption (id : U64) (status : U32) (wire : prost.encoding.wire_type.WireType)
    (before : Slice U8) (ctx : prost.encoding.DecodeContext) :
    (∃ result value after,
      prost.encoding.uint32.merge InnerResponseV1.sliceBuf wire status before ctx = .ok (result,value,after) ∧
      after.length ≤ before.length) ∧
    (∃ result value after,
      prost.encoding.uint64.merge InnerResponseV1.sliceBuf wire id before ctx = .ok (result,value,after) ∧
      after.length ≤ before.length) := by
  have varint :
      (∃ result value after,
        prost.encoding.uint32.merge InnerResponseV1.sliceBuf .Varint status before ctx = .ok (result,value,after) ∧
        after.length ≤ before.length) ∧
      (∃ result value after,
        prost.encoding.uint64.merge InnerResponseV1.sliceBuf .Varint id before ctx = .ok (result,value,after) ∧
        after.length ≤ before.length) := by
    obtain ⟨decoded,after,run,bound,strict⟩ := FullParserV3.varint_total before
    have h32 := InnerResponseV1.uint32_from_decode status before after ctx decoded run
    have h64 := InnerResponseV1.uint64_from_decode id before after ctx decoded run
    cases decoded with
    | Ok value => exact ⟨⟨_,_,_,h32,bound⟩,⟨_,_,_,h64,bound⟩⟩
    | Err error => exact ⟨⟨_,_,_,h32,bound⟩,⟨_,_,_,h64,bound⟩⟩
  cases wire <;> first
    | exact varint
    | exact ⟨⟨_,_,_,rfl,Nat.le_refl _⟩,⟨_,_,_,rfl,Nat.le_refl _⟩⟩
open LibSignalReference.Candidate.ProstSkipBuf in
theorem decoded_suffix_bound (before after : Slice U8)
    (decoded : core.result.Result U64 LoopSupportSkip.error.DecodeError)
    (hpost : PrefixPost before decoded after) (error : ErrorPost before decoded after) :
    after.length ≤ before.length := by
  cases decoded with
  | Ok value =>
    obtain ⟨count,hc,h10,hprefix,hrest⟩ := hpost
    rw [hrest,drop_length]
    omega
  | Err failure =>
    change after = if FastGuard before then before else drop before (min 10 before.length) at error
    rw [error]
    split
    · exact Nat.le_refl _
    · rw [drop_length]; omega

theorem string_result_bound (old : ActualInnerResponseV1.String)
    (decoded : core.result.Result U64 LoopSupportSkip.error.DecodeError) (after : Slice U8) :
    (InnerResponseV1.strongStringResult (StringContentV3.stringResult
      (StringContentV3.bytesResult old decoded after))).2.2.length ≤ after.length := by
  have strong (result : StringContentV3.MergeResult) :
      (InnerResponseV1.strongStringResult result).2.2 = result.2.2 := by
    rcases result with ⟨status,value,suffix⟩
    cases status <;> rfl
  rw [strong]
  have utf8 (result : StringContentV3.MergeResult) :
      (StringContentV3.stringResult result).2.2 = result.2.2 := by
    rcases result with ⟨status,value,suffix⟩
    cases status with
    | Err error => rfl
    | Ok unit => simp only [StringContentV3.stringResult]; split <;> rfl
  rw [utf8]
  cases decoded with
  | Err error => exact Nat.le_refl _
  | Ok value =>
    simp only [StringContentV3.bytesResult]
    split
    · change (LibSignalReference.Candidate.ProstBytesBuf.drop after value.val).length ≤ after.length
      simp only [LibSignalReference.Candidate.ProstBytesBuf.drop,Slice.length,List.length_drop]
      omega
    · exact Nat.le_refl _

/-- Actual strong String cleanup retains a suffix no longer than the input,
including malformed prefixes, underflow and invalid UTF8. -/
theorem string_consumption (old : ActualInnerResponseV1.String) (before : Slice U8)
    (ctx : prost.encoding.DecodeContext) :
    ∃ result value after,
      prost.encoding.string.merge InnerResponseV1.sliceBuf .LengthDelimited old before ctx = .ok (result,value,after) ∧
      after.length ≤ before.length := by
  obtain ⟨decoded,after,hpost,error,run⟩ := InnerResponseV1.string_full_reference old before ctx
  exact ⟨_,_,_,run,(string_result_bound old decoded after).trans (decoded_suffix_bound before after decoded hpost error)⟩
#print axioms decoded_suffix_bound
#print axioms string_result_bound
#print axioms string_consumption
#print axioms scalar_consumption
end ChatResponseReference.InnerScanV1
