import ProtoParseWork.FullParserV3Work.SkipErrorDomain
import ProtoParseWork.FullParserV3Work.KnownTotality
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3.Observed
open SignalMessageIntegration DispatcherIntegration
set_option maxHeartbeats 2000000

def SignalRepresented (status : core.result.Result Unit prost.error.DecodeError) : Prop :=
  ∃ encoded, statusView status = some encoded

theorem uint32_errors_represented (wire : prost.encoding.wire_type.WireType)
    (old value : U32) (before after : Slice U8) (ctx : prost.encoding.DecodeContext)
    (e : prost.error.DecodeError)
    (hd : prost.encoding.uint32.merge DispatcherIntegration.sliceBuf wire old before ctx =
      .ok (.Err e,value,after)) : SignalRepresented (.Err e) := by
  by_cases hw : wire = .Varint
  · subst wire
    obtain ⟨decoded,remaining,hp,_,hm⟩ := LibSignalReference.Candidate.ProstField.uint32_full_reference before old ⟨ctx.recurse_count⟩
    unfold prost.encoding.uint32.merge at hd
    rw [field_slice_adapter] at hd
    simp only [toFieldWire] at hd
    rw [hm] at hd
    simp only [bind_tc_ok] at hd
    cases decoded with
    | Ok n => cases hd
    | Err error =>
      have he : fieldError error = e := congrArg Prod.fst (Result.ok.inj hd) |> core.result.Result.Err.inj
      rw [← he,hp.1]
      exact ⟨⟨1,0⟩,rfl⟩
  · have hw' : toFieldWire wire ≠ .Varint := by cases wire <;> simp_all [toFieldWire]
    unfold prost.encoding.uint32.merge at hd
    rw [LibSignalReference.Candidate.ProstField.uint32_wire_error _ _ _ _ _ hw'] at hd
    have he : fieldError (LibSignalReference.Candidate.ProstField.decodeError
      (.UnexpectedWireType (toFieldWire wire) .Varint)) = e :=
      core.result.Result.Err.inj (congrArg Prod.fst (Result.ok.inj hd))
    rw [← he]
    exact ⟨_,rfl⟩

theorem bytes_errors_represented (wire : prost.encoding.wire_type.WireType)
    (old value : alloc.vec.Vec U8) (before after : Slice U8) (ctx : prost.encoding.DecodeContext)
    (e : prost.error.DecodeError)
    (hd : prost.encoding.bytes.merge alloc.vec.VecU8.Insts.ProstEncodingBytesAdapter
      DispatcherIntegration.sliceBuf wire old before ctx = .ok (.Err e,value,after)) :
    SignalRepresented (.Err e) := by
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
    | Err error =>
      have he : error = e := core.result.Result.Err.inj (congrArg Prod.fst (Result.ok.inj hd))
      rw [← he,hp.1]
      exact ⟨⟨1,0⟩,rfl⟩
    | Ok n =>
      by_cases hn : n.val ≤ remaining.length
      · simp only [LibSignalReference.Candidate.ProstBytes.bytesResult,if_pos hn] at hd
        cases hd
      · simp only [LibSignalReference.Candidate.ProstBytes.bytesResult,if_neg hn] at hd
        have he : LibSignalReference.Candidate.ProstBytes.decodeError .BufferUnderflow = e :=
          core.result.Result.Err.inj (congrArg Prod.fst (Result.ok.inj hd))
        rw [← he]
        exact ⟨⟨6,0⟩,rfl⟩
  · have hw' : toBytesWire wire ≠ .LengthDelimited := by cases wire <;> simp_all [toBytesWire]
    unfold prost.encoding.bytes.merge at hd
    rw [LibSignalReference.Candidate.ProstBytes.bytes_wire_error _ _ _ _ _ _ hw'] at hd
    have he : LibSignalReference.Candidate.ProstBytes.decodeError
      (.UnexpectedWireType (toBytesWire wire) .LengthDelimited) = e :=
      core.result.Result.Err.inj (congrArg Prod.fst (Result.ok.inj hd))
    rw [← he]
    exact ⟨_,rfl⟩

theorem uint32_status_represented (wire : prost.encoding.wire_type.WireType)
    (old value : U32) (before after : Slice U8) (ctx : prost.encoding.DecodeContext)
    (status : core.result.Result Unit prost.error.DecodeError)
    (hd : prost.encoding.uint32.merge DispatcherIntegration.sliceBuf wire old before ctx =
      .ok (status,value,after)) : SignalRepresented status := by
  cases status with
  | Ok u => cases u; exact ⟨⟨0,0⟩,rfl⟩
  | Err e => exact uint32_errors_represented wire old value before after ctx e hd

theorem bytes_status_represented (wire : prost.encoding.wire_type.WireType)
    (old value : alloc.vec.Vec U8) (before after : Slice U8) (ctx : prost.encoding.DecodeContext)
    (status : core.result.Result Unit prost.error.DecodeError)
    (hd : prost.encoding.bytes.merge alloc.vec.VecU8.Insts.ProstEncodingBytesAdapter
      DispatcherIntegration.sliceBuf wire old before ctx = .ok (status,value,after)) :
    SignalRepresented status := by
  cases status with
  | Ok u => cases u; exact ⟨⟨0,0⟩,rfl⟩
  | Err e => exact bytes_errors_represented wire old value before after ctx e hd

#print axioms bytes_errors_represented

#print axioms uint32_errors_represented
end FullParserV3.Observed
