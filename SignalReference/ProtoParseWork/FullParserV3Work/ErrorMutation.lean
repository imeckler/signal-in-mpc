import ProtoParseWork.FullParserV3Work.KnownTotality
open Aeneas Aeneas.Std Result
namespace FullParserV3
open SignalMessageIntegration DispatcherIntegration
set_option maxHeartbeats 2000000

/-- Actual scalar merger errors retain the supplied existing/default value. -/
theorem uint32_error_value (wire : prost.encoding.wire_type.WireType)
    (old value : U32) (before after : Slice U8) (ctx : prost.encoding.DecodeContext)
    (e : prost.error.DecodeError)
    (hd : prost.encoding.uint32.merge DispatcherIntegration.sliceBuf wire old before ctx =
      .ok (.Err e,value,after)) : value = old := by
  by_cases hw : wire = .Varint
  · subst wire
    obtain ⟨decoded,remaining,_,_,hm⟩ := LibSignalReference.Candidate.ProstField.uint32_full_reference before old ⟨ctx.recurse_count⟩
    unfold prost.encoding.uint32.merge at hd
    rw [field_slice_adapter] at hd
    simp only [toFieldWire] at hd
    rw [hm] at hd
    cases decoded with
    | Ok n => cases hd
    | Err error => exact (congrArg (fun x => x.2.1) (Result.ok.inj hd)).symm
  · have hw' : toFieldWire wire ≠ .Varint := by cases wire <;> simp_all [toFieldWire]
    unfold prost.encoding.uint32.merge at hd
    rw [LibSignalReference.Candidate.ProstField.uint32_wire_error _ _ _ _ _ hw'] at hd
    exact (congrArg (fun x => x.2.1) (Result.ok.inj hd)).symm

/-- Actual bytes merger errors also retain the entire existing/default vector;
no prefix or partial replacement is manufactured by the observation. -/
theorem bytes_error_value (wire : prost.encoding.wire_type.WireType)
    (old value : alloc.vec.Vec U8) (before after : Slice U8) (ctx : prost.encoding.DecodeContext)
    (e : prost.error.DecodeError)
    (hd : prost.encoding.bytes.merge alloc.vec.VecU8.Insts.ProstEncodingBytesAdapter
      DispatcherIntegration.sliceBuf wire old before ctx = .ok (.Err e,value,after)) : value = old := by
  by_cases hw : wire = .LengthDelimited
  · subst wire
    obtain ⟨decoded,remaining,_,_,hm⟩ := LibSignalReference.Candidate.ProstBytes.bytes_full_reference
      (toBytesAdapter alloc.vec.VecU8.Insts.ProstEncodingBytesAdapter).sealedBytesAdapterInst before old ctx
    have hr : prost.encoding.bytes.merge alloc.vec.VecU8.Insts.ProstEncodingBytesAdapter
        DispatcherIntegration.sliceBuf .LengthDelimited old before ctx =
      .ok (LibSignalReference.Candidate.ProstBytes.bytesResult old decoded remaining) := by
      unfold prost.encoding.bytes.merge
      rw [bytes_slice_adapter,bytes_actual_adapter]
      exact hm
    rw [hr] at hd
    cases decoded with
    | Err error => exact (congrArg (fun x => x.2.1) (Result.ok.inj hd)).symm
    | Ok n =>
      by_cases hn : n.val ≤ remaining.length
      · simp only [LibSignalReference.Candidate.ProstBytes.bytesResult,if_pos hn] at hd
        cases hd
      · simp only [LibSignalReference.Candidate.ProstBytes.bytesResult,if_neg hn] at hd
        exact (congrArg (fun x => x.2.1) (Result.ok.inj hd)).symm
  · have hw' : toBytesWire wire ≠ .LengthDelimited := by cases wire <;> simp_all [toBytesWire]
    unfold prost.encoding.bytes.merge at hd
    rw [LibSignalReference.Candidate.ProstBytes.bytes_wire_error _ _ _ _ _ _ hw'] at hd
    exact (congrArg (fun x => x.2.1) (Result.ok.inj hd)).symm

#print axioms uint32_error_value
#print axioms bytes_error_value
end FullParserV3
