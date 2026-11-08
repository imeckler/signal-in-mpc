import ProtoParseWork.FullParserV3Work.DecoderErrorTransport
import ProtoParseWork.FullParserV3Work.ErrorMutation
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open SignalMessageIntegration DispatcherIntegration
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxHeartbeats 2000000

/-- Matching-wire bytes failures are precisely prefix rejection or decoded
length underflow. Both alternatives retain the complete old vector and exact
actual decoder suffix, rather than a successful-prefix approximation. -/
theorem bytes_payload_error (old value : alloc.vec.Vec U8) (before after : Slice U8)
    (ctx : prost.encoding.DecodeContext) (error : prost.error.DecodeError)
    (hd : prost.encoding.bytes.merge alloc.vec.VecU8.Insts.ProstEncodingBytesAdapter
      DispatcherIntegration.sliceBuf .LengthDelimited old before ctx = .ok (.Err error,value,after)) :
    value = old ∧
    ((error = LibSignalReference.Candidate.ProstBytes.decodeError .InvalidVarint ∧
      LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Err invalidError,after)) ∨
     (error = LibSignalReference.Candidate.ProstBytes.decodeError .BufferUnderflow ∧
      ∃ raw : U64, LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok raw,after) ∧
        after.length < raw.val)) := by
  have hv := bytes_error_value .LengthDelimited old value before after ctx error hd
  refine ⟨hv,?_⟩
  obtain ⟨decoded,remaining,hp,he,hm⟩ := LibSignalReference.Candidate.ProstBytes.bytes_full_reference
    (toBytesAdapter alloc.vec.VecU8.Insts.ProstEncodingBytesAdapter).sealedBytesAdapterInst before old ctx
  have hr : prost.encoding.bytes.merge alloc.vec.VecU8.Insts.ProstEncodingBytesAdapter
      DispatcherIntegration.sliceBuf .LengthDelimited old before ctx =
    .ok (LibSignalReference.Candidate.ProstBytes.bytesResult old decoded remaining) := by
    unfold prost.encoding.bytes.merge
    rw [bytes_slice_adapter,bytes_actual_adapter]
    exact hm
  rw [hr] at hd
  cases decoded with
  | Err nativeError =>
    have hs := Result.ok.inj hd
    have herr : nativeError = error := core.result.Result.Err.inj (congrArg Prod.fst hs)
    have ha : remaining = after := congrArg (fun x => x.2.2) hs
    apply Or.inl
    refine ⟨?_,?_⟩
    · rw [←herr,hp.1]
      rfl
    · rw [←ha]
      exact bytes_error_to_skip before remaining nativeError hp he
  | Ok raw =>
    by_cases hn : raw.val ≤ remaining.length
    · simp only [LibSignalReference.Candidate.ProstBytes.bytesResult,if_pos hn] at hd
      cases hd
    · simp only [LibSignalReference.Candidate.ProstBytes.bytesResult,if_neg hn] at hd
      have hs := Result.ok.inj hd
      have herr : LibSignalReference.Candidate.ProstBytes.decodeError .BufferUnderflow = error :=
        core.result.Result.Err.inj (congrArg Prod.fst hs)
      have ha : remaining = after := congrArg (fun x => x.2.2) hs
      refine Or.inr ⟨herr.symm,raw,?_,?_⟩
      · rw [←ha]
        exact bytes_success_to_skip before remaining raw hp
      · rw [←ha]; omega

#print axioms bytes_payload_error
end FullParserV3
