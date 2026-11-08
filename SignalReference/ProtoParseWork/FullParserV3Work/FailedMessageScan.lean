import ProtoParseWork.FullParserV3Work.UnknownMessageRejection
import ProtoParseWork.FullParserV3Work.SuccessfulMessageScan
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3.Observed
open SignalMessageIntegration DispatcherIntegration
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

private theorem message_rejected_prefix (bytes after : Slice U8) (position middle : Nat)
    (state : State (BitVec 8) (BitVec 64)) (intermediate : ProtoParse.State (BitVec 8) (BitVec 64))
    (error : prost.error.DecodeError) (message : Message) (hp : position ≤ middle) (hb : middle ≤ bytes.length)
    (hat : StateAt bytes position state.parser []) (hmid : StateAt bytes middle intermediate [])
    (he : scanOf bytes position middle state.parser = intermediate)
    (hr : MessageRejectedScan bytes middle ⟨intermediate,state.error⟩ after error message) :
    MessageRejectedScan bytes position state after error message := by
  have hprefix := lift_successful_interval bytes position middle state intermediate hat.ok hat.fields_mask he hmid.ok
  have hscan := scan_split bytes position middle bytes.length state hp hb
  rw [hprefix] at hscan
  unfold MessageRejectedScan
  rw [hscan]
  exact hr

/-- Whole actual message-error trace composition: any successful/duplicate/
unknown/group prefixes followed by any actual malformed field or key retain
exact rejection, suffix, constructor parameters and all six mutated Options. -/
theorem failed_message_scan {message before result}
    (trace : MergeTrace ⟨100#u32⟩ message before result) :
    ∀ error, result.1 = .Err error →
    ∀ (bytes : Slice U8) (position : Nat) (state : State (BitVec 8) (BitVec 64)),
      position ≤ bytes.length → bytes.length ≤ 512 → ∀ hat : StateAt bytes position state.parser [],
      before = drop bytes position → messageView bytes state.parser.fields hat.fields_size = message →
      MessageRejectedScan bytes position state result.2.2 error result.2.1 := by
  induction trace with
  | empty => intro error hs; cases hs
  | @keyError message before after native hn hk =>
    intro error hs
    cases hs
    intro bytes position state hb hcap hat hbefore hview
    have hp : position < bytes.length := by rw [hbefore,drop_length] at hn; omega
    unfold ActualMessageDriver.prost.encoding.decode_key at hk
    obtain ⟨r,remaining,hr,_,_⟩ := key_total before
    rw [driver_skip_adapter,hr] at hk
    cases r with
    | Ok pair => cases hk
    | Err err =>
      have hkey : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Err err,remaining) := by
        simpa only [hbefore] using hr
      cases hk
      exact message_rejected_of_scan bytes _ position state (skipError err) state.parser.fields message
        hat.fields_size hat.fields_mask hview (key_failure_scan bytes _ position err state [] hp hcap hat hkey)
  | @fieldError message before middle after native next tag wire hn hk hm =>
    intro error hs
    cases hs
    intro bytes position state hb hcap hat hbefore hview
    have hp : position < bytes.length := by rw [hbefore,drop_length] at hn; omega
    unfold ActualMessageDriver.prost.encoding.decode_key at hk
    obtain ⟨r,remaining,hr,_,_⟩ := key_total before
    rw [driver_skip_adapter,hr] at hk
    cases r with
    | Err err => cases hk
    | Ok pair =>
      rcases pair with ⟨t,k⟩
      obtain ⟨value,count,hvalid,htag,_,_,_,_,_⟩ := decode_key_success before remaining t k hr
      have ht : 0 < t.val := by have h := hvalid.2.1; omega
      have hkey : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (t,k),remaining) := by
        simpa only [hbefore] using hr
      cases hk
      by_cases hknown : tag.val ≤ 6
      · exact known_message_rejected_scan bytes middle after position tag k native state message next ⟨100#u32⟩ hp hcap hat hview ht hknown hkey hm
      · exact unknown_message_rejected_scan bytes middle after position tag k native state message next hp hcap hat hview (by omega) hkey hm
  | @next message before middle after next tag wire result hn hk hm rest ih =>
    intro error hs
    intro bytes position state hb hcap hat hbefore hview
    have hp : position < bytes.length := by rw [hbefore,drop_length] at hn; omega
    unfold ActualMessageDriver.prost.encoding.decode_key at hk
    obtain ⟨r,remaining,hr,_,_⟩ := key_total before
    rw [driver_skip_adapter,hr] at hk
    cases r with
    | Err err => cases hk
    | Ok pair =>
      rcases pair with ⟨t,k⟩
      obtain ⟨value,count,hvalid,htag,_,_,_,_,_⟩ := decode_key_success before remaining t k hr
      have ht : 0 < t.val := by have h := hvalid.2.1; omega
      have hkey : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (t,k),remaining) := by
        simpa only [hbefore] using hr
      cases hk
      have hfield : MessageScan bytes position state.parser after next := by
        by_cases hknown : tag.val ≤ 6
        · exact known_message_scan bytes middle after position tag k state.parser message next ⟨100#u32⟩ hp hcap hat hview ht hknown hkey hm
        · exact unknown_message_scan bytes middle after position tag k state.parser message next hp hcap hat hview (by omega) hkey hm
      obtain ⟨mid,intermediate,hp',hmid,hafter,hscan,hat',hview'⟩ := hfield
      have hrest := ih error hs bytes mid ⟨intermediate,state.error⟩ hmid hcap hat' hafter hview'
      exact message_rejected_prefix bytes result.2.2 position mid state intermediate error result.2.1 hp'.le hmid hat hat' hscan hrest

#print axioms failed_message_scan
end FullParserV3.Observed
