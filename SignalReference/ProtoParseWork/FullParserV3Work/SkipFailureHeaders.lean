import ProtoParseWork.FullParserV3Work.SkipFailureLeaves
import ProtoParseWork.FullParserV3Work.EndGroupRejectionStep
import ProtoParseWork.FullParserV3Work.EOFRejectedScan
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3.Observed
open SignalMessageIntegration DispatcherIntegration
open LibSignalReference.Candidate.ProstSkipBuf
set_option maxHeartbeats 3000000

theorem key_failure_scan (bytes after : Slice U8) (position : Nat) (error : LoopSupportSkip.error.DecodeError)
    (state : State (BitVec 8) (BitVec 64)) (tags : List U32) (hp : position < bytes.length) (hcap : bytes.length ≤ 512)
    (hat : StateAt bytes position state.parser tags)
    (hd : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Err error,after)) :
    RejectedScan bytes position state after (skipError error) state.parser.fields := by
  let key := (rowsOf bytes)[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩
  let payload := ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete key.stop (position+1) (((rowsOf bytes).drop (position+1)).take 10)
  let p := planOf bytes position state.parser
  have hp' := actual_key_rejection_plan bytes after position error payload state.parser hp hcap hd
  have hp0 : p.ok = 0 := hp'.1
  have ht0 : p.tag = 0 := hp'.2.1
  have hn := apply_key_reject position p state.parser hat.ok hat.cursor hp0 ht0 (by have h := hat.fields_size; omega)
  have hparser : (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes) state position).parser =
      ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state.parser := rfl
  apply active_remaining_scan bytes after position (skipError error) state state.parser.fields tags hp hat.frames
  intro positions
  have ho := actual_key_rejection_step bytes after position error state hp hcap hat.ok hat.cursor hat.fields_size hd positions
  have hf := scan_failed bytes.length positions (rowsOf bytes) (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes) state position)
    (by rw [hparser]; exact hn.1)
  rw [hf] at ho
  change _ ∧ _ ∧ _ ∧ _ ∧ _ at ho
  obtain ⟨h1,h2,h3,h4,h5⟩ := ho
  rw [hf,finish_failed _ h1]
  refine ⟨h1,h2,h3,?_,?_,h4,h5⟩
  · rw [hparser]; exact hn.2.2.1
  · rw [hparser]; exact hn.2.2.2.1

theorem mismatched_group_failure_scan (bytes middle after : Slice U8) (position : Nat) (outer inner count : U32)
    (error : LoopSupportSkip.error.DecodeError) (state : State (BitVec 8) (BitVec 64)) (tags : List U32)
    (hp : position < bytes.length) (hcap : bytes.length ≤ 512) (hat : StateAt bytes position state.parser (tags++[outer]))
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (inner,.EndGroup),middle))
    (hb : LoopSupportSkip.encoding.skip_field_loop.body sliceBuf outer ⟨count⟩ (drop bytes position) = .ok (.done (.Err error,after))) :
    RejectedScan bytes position state after (skipError error) state.parser.fields :=
  active_remaining_scan bytes after position (skipError error) state state.parser.fields (tags++[outer]) hp hat.frames
    (actual_group_end_rejection_step bytes middle after position outer inner count tags error state hp hcap hat.ok hat.cursor hat.frames hk hb)

theorem top_end_failure_scan (bytes middle after : Slice U8) (position : Nat) (tag count : U32)
    (error : LoopSupportSkip.error.DecodeError) (state : State (BitVec 8) (BitVec 64))
    (hp : position < bytes.length) (hcap : bytes.length ≤ 512) (hat : StateAt bytes position state.parser [])
    (ht : 6 < tag.val) (hc : count ≠ 0#u32)
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,.EndGroup),middle))
    (hd : LoopSupportSkip.encoding.skip_field sliceBuf .EndGroup tag middle ⟨count⟩ = .ok (.Err error,after)) :
    RejectedScan bytes position state after (skipError error) state.parser.fields :=
  active_remaining_scan bytes after position (skipError error) state state.parser.fields [] hp hat.frames
    (actual_top_end_rejection_step bytes middle after position tag count error state hp hcap hat.ok hat.cursor hat.fields_size
      hat.frames.depth_eq ht hc hk hd)

#print axioms key_failure_scan
#print axioms mismatched_group_failure_scan
#print axioms top_end_failure_scan
end FullParserV3.Observed
