import ProtoParseWork.FullParserV3Work.DecoderErrorTransport
import ProtoParseWork.FullParserV3Work.ErrorMutation
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open SignalMessageIntegration DispatcherIntegration
set_option maxHeartbeats 2000000

/-- A matching-wire actual scalar failure is exactly the independently refined
payload decoder failure, including its fast/slow consumed suffix and old value. -/
theorem scalar_payload_error (old value : U32) (before after : Slice U8)
    (ctx : prost.encoding.DecodeContext) (error : prost.error.DecodeError)
    (hd : prost.encoding.uint32.merge DispatcherIntegration.sliceBuf .Varint old before ctx =
      .ok (.Err error,value,after)) :
    error = fieldError (LibSignalReference.Candidate.ProstField.decodeError .InvalidVarint) ∧
    value = old ∧ LoopSupportSkip.encoding.varint.decode_varint
      LibSignalReference.Candidate.ProstSkipBuf.sliceBuf before =
      .ok (.Err LibSignalReference.Candidate.ProstSkipSlice.invalidError,after) := by
  obtain ⟨decoded,remaining,hp,he,hm⟩ := LibSignalReference.Candidate.ProstField.uint32_full_reference before old ⟨ctx.recurse_count⟩
  unfold prost.encoding.uint32.merge at hd
  rw [field_slice_adapter] at hd
  simp only [toFieldWire] at hd
  rw [hm] at hd
  cases decoded with
  | Ok n => cases hd
  | Err nativeError =>
    have hs := Result.ok.inj hd
    have herr : fieldError nativeError = error := core.result.Result.Err.inj (congrArg Prod.fst hs)
    have hv : old = value := congrArg (fun x => x.2.1) hs
    have ha : remaining = after := congrArg (fun x => x.2.2) hs
    refine ⟨?_,hv.symm,?_⟩
    · rw [←herr,hp.1]
      rfl
    · rw [←ha]
      exact field_error_to_skip before remaining nativeError hp he

#print axioms scalar_payload_error
end FullParserV3
