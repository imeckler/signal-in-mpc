import ProtoParseWork.FullParserV3Work.DecoderTransport
open Aeneas Aeneas.Std Result
namespace FullParserV3
open SignalMessageIntegration DispatcherIntegration
open LibSignalReference.Candidate.ProstSkipBuf
set_option maxHeartbeats 2000000

theorem uint32_success_value (wire : prost.encoding.wire_type.WireType)
    (old value : U32) (before after : Slice U8) (ctx : prost.encoding.DecodeContext)
    (hd : prost.encoding.uint32.merge DispatcherIntegration.sliceBuf wire old before ctx = .ok (.Ok (),value,after)) :
    wire = .Varint ∧ ∃ raw, LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok raw,after) ∧
      value = UScalar.cast .U32 raw := by
  by_cases hw : wire = .Varint
  · subst wire
    obtain ⟨decoded,remaining,hp,_,hm⟩ := LibSignalReference.Candidate.ProstField.uint32_full_reference before old ⟨ctx.recurse_count⟩
    unfold prost.encoding.uint32.merge at hd
    rw [field_slice_adapter] at hd
    simp only [toFieldWire] at hd
    rw [hm] at hd
    cases decoded with
    | Err error => cases hd
    | Ok raw =>
      have hv := congrArg (fun x => x.2.1) (Result.ok.inj hd)
      have ha := congrArg (fun x => x.2.2) (Result.ok.inj hd)
      change remaining = after at ha
      refine ⟨rfl,raw,?_,hv.symm⟩
      simpa only [ha] using field_success_to_skip before remaining raw hp
  · have hw' : toFieldWire wire ≠ .Varint := by cases wire <;> simp_all [toFieldWire]
    unfold prost.encoding.uint32.merge at hd
    rw [LibSignalReference.Candidate.ProstField.uint32_wire_error _ _ _ _ _ hw'] at hd
    cases hd

theorem bytes_success_value (wire : prost.encoding.wire_type.WireType)
    (old value : alloc.vec.Vec U8) (before after : Slice U8) (ctx : prost.encoding.DecodeContext)
    (hd : prost.encoding.bytes.merge alloc.vec.VecU8.Insts.ProstEncodingBytesAdapter
      DispatcherIntegration.sliceBuf wire old before ctx = .ok (.Ok (),value,after)) :
    wire = .LengthDelimited ∧ ∃ raw remaining,
      LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok raw,remaining) ∧
      raw.val ≤ remaining.length ∧ value = LibSignalReference.Candidate.ProstVecAdapter.fromSlice
        (ProstBytesCandidate.ContentModel.take remaining raw.val) ∧
      after = LibSignalReference.Candidate.ProstBytesBuf.drop remaining raw.val := by
  by_cases hw : wire = .LengthDelimited
  · subst wire
    obtain ⟨decoded,remaining,hp,_,hm⟩ := LibSignalReference.Candidate.ProstBytes.bytes_full_reference
      (toBytesAdapter alloc.vec.VecU8.Insts.ProstEncodingBytesAdapter).sealedBytesAdapterInst before old ctx
    have hr : prost.encoding.bytes.merge alloc.vec.VecU8.Insts.ProstEncodingBytesAdapter
        DispatcherIntegration.sliceBuf .LengthDelimited old before ctx =
      .ok (LibSignalReference.Candidate.ProstBytes.bytesResult old decoded remaining) := by
      unfold prost.encoding.bytes.merge
      rw [bytes_slice_adapter,bytes_actual_adapter]
      exact hm
    rw [hr] at hd
    cases decoded with
    | Err error => cases hd
    | Ok raw =>
      by_cases hn : raw.val ≤ remaining.length
      · simp only [LibSignalReference.Candidate.ProstBytes.bytesResult,if_pos hn] at hd
        exact ⟨rfl,raw,remaining,bytes_success_to_skip before remaining raw hp,hn,
          (congrArg (fun x => x.2.1) (Result.ok.inj hd)).symm,
          (congrArg (fun x => x.2.2) (Result.ok.inj hd)).symm⟩
      · simp only [LibSignalReference.Candidate.ProstBytes.bytesResult,if_neg hn] at hd
        cases hd
  · have hw' : toBytesWire wire ≠ .LengthDelimited := by cases wire <;> simp_all [toBytesWire]
    unfold prost.encoding.bytes.merge at hd
    rw [LibSignalReference.Candidate.ProstBytes.bytes_wire_error _ _ _ _ _ _ hw'] at hd
    cases hd

#print axioms uint32_success_value
#print axioms bytes_success_value
end FullParserV3
