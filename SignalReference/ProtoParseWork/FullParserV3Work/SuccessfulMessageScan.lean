import ProtoParseWork.FullParserV3Work.UnknownMessageScan
import ProtoParseWork.FullParserV3Work.MessageSuffix
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open SignalMessageIntegration DispatcherIntegration
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

/-- Complete successful actual merge-loop scan composition. The empty-loop
case forces the absolute cursor to the whole body's end. Every successful
known/duplicate/unknown/group transition preserves the six-field observation. -/
theorem successful_message_scan {message before result}
    (trace : MergeTrace ⟨100#u32⟩ message before result) (hs : result.1 = .Ok ()) :
    ∀ (bytes : Slice U8) (position : Nat) (state : ProtoParse.State (BitVec 8) (BitVec 64)),
      position ≤ bytes.length → bytes.length ≤ 512 → ∀ hat : StateAt bytes position state [],
      before = drop bytes position → messageView bytes state.fields hat.fields_size = message →
      ∃ finalState, scanOf bytes position bytes.length state = finalState ∧
        ∃ hfinal : StateAt bytes bytes.length finalState [], result.2.2 = drop bytes bytes.length ∧
        messageView bytes finalState.fields hfinal.fields_size = result.2.1 := by
  induction trace with
  | empty message before hempty =>
    intro bytes position state hb hcap hat hbefore hview
    have hp : position = bytes.length := by rw [hbefore,drop_length] at hempty; omega
    subst position
    refine ⟨state,?_,hat,hbefore,hview⟩
    simp only [scanOf,Nat.sub_self,List.range'_zero,List.foldl_nil]
  | keyError => cases hs
  | fieldError => cases hs
  | @next message before middle after next tag wire result hn hk hm rest ih =>
    intro bytes position state hb hcap hat hbefore hview
    have hp : position < bytes.length := by rw [hbefore,drop_length] at hn; omega
    unfold ActualMessageDriver.prost.encoding.decode_key at hk
    obtain ⟨r,remaining,hr,_,_⟩ := key_total before
    rw [driver_skip_adapter,hr] at hk
    cases r with
    | Err error => cases hk
    | Ok pair =>
      rcases pair with ⟨t,k⟩
      obtain ⟨value,count,hvalid,htag,_,_,_,_,_⟩ := decode_key_success before remaining t k hr
      have ht : 0 < t.val := by have h := hvalid.2.1; omega
      have hkey : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (t,k),remaining) := by
        simpa only [hbefore] using hr
      cases hk
      have hfield : MessageScan bytes position state after next := by
        by_cases hknown : tag.val ≤ 6
        · exact known_message_scan bytes middle after position tag k state message next ⟨100#u32⟩ hp hcap hat hview ht hknown hkey hm
        · exact unknown_message_scan bytes middle after position tag k state message next hp hcap hat hview (by omega) hkey hm
      obtain ⟨mid,intermediate,hp',hmid,hafter,hscan,hat',hview'⟩ := hfield
      obtain ⟨finalState,htail,hfinal,hrest,hresult⟩ := ih hs bytes mid intermediate hmid hcap hat' hafter hview'
      refine ⟨finalState,?_,hfinal,hrest,hresult⟩
      unfold scanOf at *
      rw [scan_split bytes.length position mid bytes.length (rowsOf bytes) state (by omega) hmid,hscan,htail]

#print axioms successful_message_scan
end FullParserV3
