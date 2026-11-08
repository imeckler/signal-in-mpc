import ProtoParseWork.FullParserV3Work.RejectedScan
import ProtoParseWork.FullParserV3Work.EOFRejection
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3.Observed
open LibSignalReference.Candidate.ProstSkipBuf
set_option maxHeartbeats 2000000

theorem eof_rejected_scan (bytes after : Slice U8) (error : LoopSupportSkip.error.DecodeError)
    (state : State (BitVec 8) (BitVec 64)) (tags : List U32)
    (hcap : bytes.length ≤ 512) (hat : StateAt bytes bytes.length state.parser tags) (hn : tags ≠ [])
    (hd : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes bytes.length) = .ok (.Err error,after)) :
    RejectedScan bytes bytes.length state after (SignalMessageIntegration.skipError error) state.parser.fields := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7⟩ := actual_eof_group_rejection bytes after error state tags hcap hat hn hd
  unfold RejectedScan scan
  simp only [Nat.sub_self,List.range'_zero,List.foldl_nil]
  refine ⟨h2,Or.inr ⟨h1,?_⟩,h3,h4,h5,h7,?_⟩
  · exact hat.nested hn
  · exact ⟨tags,hat.frames⟩

#print axioms eof_rejected_scan
end FullParserV3.Observed
