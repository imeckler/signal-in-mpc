import ProtoParseWork.FullParserV3Work.ActualFailedSkipScan
import ProtoParseWork.FullParserV3Work.MessageRejected
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3.Observed
open SignalMessageIntegration DispatcherIntegration
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkip
set_option maxHeartbeats 3000000

theorem unknown_message_rejected_scan (bytes middle after : Slice U8) (position : Nat) (tag : U32)
    (kind : LoopSupportSkip.encoding.wire_type.WireType) (error : prost.error.DecodeError)
    (state : State (BitVec 8) (BitVec 64)) (message next : Message)
    (hp : position < bytes.length) (hcap : bytes.length ≤ 512) (hat : StateAt bytes position state.parser [])
    (hv : messageView bytes state.parser.fields hat.fields_size = message) (ht : 6 < tag.val)
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,kind),middle))
    (hm : proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field DispatcherIntegration.sliceBuf
      message tag (signalWire kind) middle ⟨100#u32⟩ = .ok (.Err error,next,after)) :
    MessageRejectedScan bytes position state after error next := by
  obtain ⟨result,hsem,hskip,_⟩ := skip_field_total kind tag 100#u32 middle
  rcases result with ⟨r,remaining⟩
  rw [unknown_dispatch _ _ _ _ _ _ ht] at hm
  unfold prost.encoding.skip_field at hm
  have hw : toSkipWire (signalWire kind) = kind := by cases kind <;> rfl
  rw [skip_slice_adapter,hw,hskip] at hm
  cases r with
  | Ok u => cases hm
  | Err native =>
    cases hm
    have hr := actual_skipped_failure_scan bytes middle _ position tag 100#u32 kind native state [] hp hcap hat (by decide)
      (Or.inr ht) (Or.inr rfl) hk hskip
    exact message_rejected_of_scan bytes _ position state (skipError native) state.parser.fields message
      hat.fields_size hat.fields_mask hv hr

#print axioms unknown_message_rejected_scan
end FullParserV3.Observed
