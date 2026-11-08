import ProtoParseWork.FullParserV3Work.MessageErrorDomain
import ProtoParseWork.FullParserV3Work.TraceUniqueness
open Aeneas Aeneas.Std Result
namespace FullParserV3.Observed
open SignalMessageIntegration DispatcherIntegration
open LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 2000000

/-- Every complete actual message trace, including every nested malformed field,
has an injectively represented error constructor/payload (or success code0). -/
theorem trace_status_represented {ctx message before result}
    (trace : MergeTrace ctx message before result) : SignalRepresented result.1 := by
  induction trace with
  | empty => exact ⟨⟨0,0⟩,rfl⟩
  | @keyError message before after e hn hk =>
    unfold ActualMessageDriver.prost.encoding.decode_key at hk
    obtain ⟨r,remaining,hr,_,_⟩ := key_total before
    rw [driver_skip_adapter,hr] at hk
    cases r with
    | Ok pair => cases hk
    | Err error =>
      have hs := key_error_represented before remaining error hr
      cases hk
      exact hs
  | @fieldError message before middle after e next tag wire hn hk hm =>
    unfold ActualMessageDriver.prost.encoding.decode_key at hk
    obtain ⟨r,remaining,hr,_,_⟩ := key_total before
    rw [driver_skip_adapter,hr] at hk
    cases r with
    | Err error => cases hk
    | Ok pair =>
      rcases pair with ⟨t,k⟩
      obtain ⟨value,count,hv,htag,_,_,_,_,_⟩ := decode_key_success before remaining t k hr
      have ht : 0 < t.val := by have h := hv.2.1; omega
      cases hk
      exact message_status_represented _ _ _ _ _ _ _ _ ht hm
  | next _ _ _ _ ih => exact ih

#print axioms trace_status_represented
end FullParserV3.Observed
