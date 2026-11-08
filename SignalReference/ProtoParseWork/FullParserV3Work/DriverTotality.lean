import ProtoParseWork.FullParserV3Work.DriverTrace
open Aeneas Aeneas.Std Result
open SignalMessageIntegration
namespace FullParserV3
open LibSignalReference.Candidate.ProstSkipKey LibSignalReference.Candidate.ProstSkipBuf
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

theorem merge_trace_total (ctx : ActualMessageDriver.prost.encoding.DecodeContext) (size : Nat) :
    ∀ (before : Slice U8) (message : Message), before.length = size →
      ∃ result, MergeTrace ctx message before result ∧ result.2.2.length ≤ before.length := by
  induction size using Nat.strong_induction_on with
  | h size ih =>
    intro before message hs
    by_cases hz : before.length = 0
    · exact ⟨_,MergeTrace.empty message before hz,Nat.le_refl _⟩
    · have hn : 0 < before.length := by omega
      obtain ⟨decoded,middle,hkey,hle,hstrict⟩ := key_total before
      cases decoded with
      | Err error =>
        have hk : ActualMessageDriver.prost.encoding.decode_key driverBuf before =
            ok (.Err (skipError error),middle) := by
          unfold ActualMessageDriver.prost.encoding.decode_key
          rw [driver_skip_adapter,hkey]
          rfl
        exact ⟨_,MergeTrace.keyError hn hk,hle⟩
      | Ok pair =>
        rcases pair with ⟨tag,kind⟩
        have hmshort := hstrict (tag,kind) rfl
        obtain ⟨value,count,hv,htag,_,_,_,_,_⟩ := decode_key_success before middle tag kind hkey
        have ht : 0 < tag.val := by have hp := hv.2.1; omega
        have hk : ActualMessageDriver.prost.encoding.decode_key driverBuf before =
            ok (.Ok (tag,ActualMessageDriver.wireFromSkip kind),middle) := by
          unfold ActualMessageDriver.prost.encoding.decode_key
          rw [driver_skip_adapter,hkey]
          rfl
        obtain ⟨status,next,after,hm,hafter⟩ := message_field_total message tag
          (wireToSignal (ActualMessageDriver.wireFromSkip kind)) middle ⟨ctx.recurse_count⟩ ht
        cases status with
        | Err error => exact ⟨_,MergeTrace.fieldError hn hk hm,hafter.trans hle⟩
        | Ok value =>
          cases value
          obtain ⟨result,htrace,hrest⟩ := ih after.length (by omega) after next rfl
          exact ⟨result,MergeTrace.next hn hk hm htrace,hrest.trans (hafter.trans hle)⟩

/-- Total actual extracted Prost Message::merge for the generated Signal
field dispatcher. The accompanying trace retains the exact suffix and fields. -/
theorem actual_merge_total (unused : ActualMessageDriver.prost.message.Message Message)
    (message : Message) (before : Slice U8) :
    ∃ result,
      MergeTrace (⟨100#u32⟩ : ActualMessageDriver.prost.encoding.DecodeContext) message before result ∧
      ActualMessageDriver.prost.message.Message.merge.default (withDispatcher unused) driverBuf message before =
        ok (result.1,result.2.1) ∧ result.2.2.length ≤ before.length := by
  obtain ⟨result,htrace,hle⟩ := merge_trace_total ⟨100#u32⟩ before.length before message rfl
  refine ⟨result,htrace,?_,hle⟩
  simp only [ActualMessageDriver.prost.message.Message.merge.default,
    ActualMessageDriver.prost.encoding.DecodeContext.Insts.CoreDefaultDefault.default,
    ActualMessageDriver.prost.RECURSION_LIMIT,bind_tc_ok]
  change ActualMessageDriver.prost.message.Message.merge.default_loop (withDispatcher unused) driverBuf message before ⟨100#u32⟩ = _
  exact trace_actual_loop unused htrace

#print axioms merge_trace_total
#print axioms actual_merge_total
end FullParserV3
