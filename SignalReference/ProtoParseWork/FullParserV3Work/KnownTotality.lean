import ProtoParseWork.FullParserV3Work.DispatcherTotality
open Aeneas Aeneas.Std Result
open SignalMessageIntegration DispatcherIntegration
namespace FullParserV3
set_option maxHeartbeats 1000000

theorem field_decoder_bound (before after : Slice U8)
    (decoded : core.result.Result U64 ProstFieldCandidate.error.DecodeError)
    (hp : LibSignalReference.Candidate.ProstFieldBuf.PrefixPost before decoded after)
    (he : LibSignalReference.Candidate.ProstFieldBuf.ErrorPost before decoded after) :
    after.length ≤ before.length := by
  cases decoded with
  | Ok value => obtain ⟨count,_,_,_,hr⟩ := hp; rw [hr,LibSignalReference.Candidate.ProstFieldBuf.drop_length]; omega
  | Err error =>
    have hr : after = if LibSignalReference.Candidate.ProstFieldBuf.FastGuard before then before
      else LibSignalReference.Candidate.ProstFieldBuf.drop before (min 10 before.length) := he
    rw [hr]; split <;> try simp only [LibSignalReference.Candidate.ProstFieldBuf.drop_length]
    all_goals omega

theorem bytes_decoder_bound (before after : Slice U8)
    (decoded : core.result.Result U64 ProstBytesCandidate.error.DecodeError)
    (hp : LibSignalReference.Candidate.ProstBytesBuf.PrefixPost before decoded after)
    (he : LibSignalReference.Candidate.ProstBytesBuf.ErrorPost before decoded after) :
    after.length ≤ before.length := by
  cases decoded with
  | Ok value => obtain ⟨count,_,_,_,hr⟩ := hp; rw [hr,LibSignalReference.Candidate.ProstBytesBuf.drop_length]; omega
  | Err error =>
    have hr : after = if LibSignalReference.Candidate.ProstBytesBuf.FastGuard before then before
      else LibSignalReference.Candidate.ProstBytesBuf.drop before (min 10 before.length) := he
    rw [hr]; split <;> try simp only [LibSignalReference.Candidate.ProstBytesBuf.drop_length]
    all_goals omega

theorem uint32_merge_total (wire : prost.encoding.wire_type.WireType)
    (old : U32) (before : Slice U8) (ctx : prost.encoding.DecodeContext) :
    ∃ status value after, prost.encoding.uint32.merge DispatcherIntegration.sliceBuf wire old before ctx =
      ok (status,value,after) ∧ after.length ≤ before.length := by
  by_cases hw : wire = .Varint
  · subst wire
    obtain ⟨decoded,after,hp,he,hm⟩ := LibSignalReference.Candidate.ProstField.uint32_full_reference before old ⟨ctx.recurse_count⟩
    have hle := field_decoder_bound before after decoded hp he
    cases decoded with
    | Ok value =>
      refine ⟨.Ok (),UScalar.cast .U32 value,after,?_,hle⟩
      unfold prost.encoding.uint32.merge
      rw [field_slice_adapter]
      simp only [toFieldWire]
      rw [hm]
      rfl
    | Err error =>
      refine ⟨.Err (fieldError error),old,after,?_,hle⟩
      unfold prost.encoding.uint32.merge
      rw [field_slice_adapter]
      simp only [toFieldWire]
      rw [hm]
      rfl
  · have hw' : toFieldWire wire ≠ .Varint := by cases wire <;> simp_all [toFieldWire]
    refine ⟨.Err (fieldError (LibSignalReference.Candidate.ProstField.decodeError
        (.UnexpectedWireType (toFieldWire wire) .Varint))),old,before,?_,Nat.le_refl _⟩
    unfold prost.encoding.uint32.merge
    rw [LibSignalReference.Candidate.ProstField.uint32_wire_error _ _ _ _ _ hw']
    rfl

theorem bytes_merge_total (wire : prost.encoding.wire_type.WireType)
    (old : alloc.vec.Vec U8) (before : Slice U8) (ctx : prost.encoding.DecodeContext) :
    ∃ status value after,
      prost.encoding.bytes.merge alloc.vec.VecU8.Insts.ProstEncodingBytesAdapter
        DispatcherIntegration.sliceBuf wire old before ctx = ok (status,value,after) ∧
      after.length ≤ before.length := by
  by_cases hw : wire = .LengthDelimited
  · subst wire
    obtain ⟨decoded,after,hp,he,hm⟩ := LibSignalReference.Candidate.ProstBytes.bytes_full_reference
      (toBytesAdapter alloc.vec.VecU8.Insts.ProstEncodingBytesAdapter).sealedBytesAdapterInst before old ctx
    have hle := bytes_decoder_bound before after decoded hp he
    have hr : prost.encoding.bytes.merge alloc.vec.VecU8.Insts.ProstEncodingBytesAdapter
        DispatcherIntegration.sliceBuf .LengthDelimited old before ctx =
      ok (LibSignalReference.Candidate.ProstBytes.bytesResult old decoded after) := by
      unfold prost.encoding.bytes.merge
      rw [bytes_slice_adapter,bytes_actual_adapter]
      exact hm
    cases decoded with
    | Err error => exact ⟨.Err error,old,after,hr,hle⟩
    | Ok value =>
      by_cases hn : value.val ≤ after.length
      · refine ⟨.Ok (),LibSignalReference.Candidate.ProstVecAdapter.fromSlice
          (ProstBytesCandidate.ContentModel.take after value.val),
          LibSignalReference.Candidate.ProstBytesBuf.drop after value.val,?_,?_⟩
        · simpa only [LibSignalReference.Candidate.ProstBytes.bytesResult,if_pos hn] using hr
        · rw [LibSignalReference.Candidate.ProstBytesBuf.drop_length]; omega
      · refine ⟨.Err (LibSignalReference.Candidate.ProstBytes.decodeError .BufferUnderflow),old,after,?_,hle⟩
        simpa only [LibSignalReference.Candidate.ProstBytes.bytesResult,if_neg hn] using hr
  · have hw' : toBytesWire wire ≠ .LengthDelimited := by cases wire <;> simp_all [toBytesWire]
    refine ⟨.Err (LibSignalReference.Candidate.ProstBytes.decodeError
      (.UnexpectedWireType (toBytesWire wire) .LengthDelimited)),old,before,?_,Nat.le_refl _⟩
    unfold prost.encoding.bytes.merge
    rw [LibSignalReference.Candidate.ProstBytes.bytes_wire_error _ _ _ _ _ _ hw']

#print axioms uint32_merge_total
#print axioms bytes_merge_total
end FullParserV3
