import ProtoParseWork.FullParserV3Work.DriverTotality
import ProtoParseWork.FullParserV3Work.MessageSuffix
open Aeneas Aeneas.Std Result
namespace FullParserV3
set_option maxHeartbeats 1000000

theorem trace_deterministic {ctx message before left right}
    (hl : MergeTrace ctx message before left) (hr : MergeTrace ctx message before right) : left = right := by
  induction hl generalizing right with
  | empty message before h => cases hr <;> simp_all
  | keyError hn hk => cases hr <;> simp_all
  | fieldError hn hk hm => cases hr <;> simp_all
  | next hn hk hm rest ih =>
    cases hr <;> simp_all
    rcases right with ⟨r,m,b⟩
    exact ih r m b (by assumption)

/-- Total, unique, suffix-retaining actual implementation semantics. This
packages the real extracted loop result together with its unique local buffer
trace; malformed input keeps both partial fields and exact input suffix. -/
theorem actual_merge_observation (unused : ActualMessageDriver.prost.message.Message Message)
    (message : Message) (before : Slice U8) :
    ∃ result,
      MergeTrace (⟨100#u32⟩ : ActualMessageDriver.prost.encoding.DecodeContext) message before result ∧
      ActualMessageDriver.prost.message.Message.merge.default (withDispatcher unused) driverBuf message before =
        ok (result.1,result.2.1) ∧ IsSuffix before result.2.2 ∧
      ∀ other, MergeTrace (⟨100#u32⟩ : ActualMessageDriver.prost.encoding.DecodeContext) message before other → other = result := by
  obtain ⟨result,ht,hr,_⟩ := actual_merge_total unused message before
  exact ⟨result,ht,hr,merge_trace_suffix ht,fun other ho => trace_deterministic ho ht⟩

#print axioms trace_deterministic
#print axioms actual_merge_observation
end FullParserV3
