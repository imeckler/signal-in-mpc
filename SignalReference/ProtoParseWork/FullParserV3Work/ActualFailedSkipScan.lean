import ProtoParseWork.FullParserV3Work.FailedSkipScan
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3.Observed
open SignalMessageIntegration DispatcherIntegration
open LoopSupportSkip LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkip
set_option maxHeartbeats 3000000

/-- Actual skip failure refinement, with finite derivation and primitive/loop
termination premises removed by the constructive totality proof. -/
theorem actual_skipped_failure_scan (bytes middle after : Slice U8) (position : Nat) (tag count : U32)
    (kind : encoding.wire_type.WireType) (error : LoopSupportSkip.error.DecodeError)
    (state : State (BitVec 8) (BitVec 64)) (tags : List U32) (hp : position < bytes.length) (hcap : bytes.length ≤ 512)
    (hat : StateAt bytes position state.parser tags) (hbudget : count.val+tags.length = 100)
    (ha : state.parser.depth ≠ 0 ∨ 6 < tag.val) (hend : kind ≠ .EndGroup ∨ tags = [])
    (hk : encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,kind),middle))
    (hd : encoding.skip_field sliceBuf kind tag middle ⟨count⟩ = .ok (.Err error,after)) :
    RejectedScan bytes position state after (skipError error) state.parser.fields := by
  obtain ⟨result,hsem,hr,_⟩ := skip_field_total kind tag count middle
  rw [hd] at hr
  cases hr
  exact failed_skip_scan hsem error rfl bytes position state tags hp hcap hat hbudget ha hend hk

/-- Actual group-loop rejection includes nested/mismatched/EOF cases with its
precise recursion budget and all current fields, not just ordinary leaves. -/
theorem actual_group_failure_scan (bytes before after : Slice U8) (position : Nat) (tag count : U32)
    (error : LoopSupportSkip.error.DecodeError) (state : State (BitVec 8) (BitVec 64)) (tags : List U32)
    (hp : position ≤ bytes.length) (hcap : bytes.length ≤ 512) (hat : StateAt bytes position state.parser (tags++[tag]))
    (hbudget : count.val+tags.length = 100) (hbefore : before = drop bytes position)
    (hd : encoding.skip_field_loop sliceBuf tag before ⟨count⟩ = .ok (.Err error,after)) :
    RejectedScan bytes position state after (skipError error) state.parser.fields := by
  have hb : tags.length+1 ≤ 100 := by simpa only [List.length_append,List.length_singleton] using hat.frames.bound.trans hat.frames.limit
  have hc : count ≠ 0#u32 := by intro hz; rw [hz] at hbudget; change 0+tags.length = 100 at hbudget; omega
  obtain ⟨result,hsem,hr,_⟩ := skip_group_total tag count before hc
  rw [hd] at hr
  cases hr
  exact failed_skip_scan hsem error rfl bytes position state tags hp hcap hat hbudget hbefore

#print axioms actual_skipped_failure_scan
#print axioms actual_group_failure_scan
end FullParserV3.Observed
