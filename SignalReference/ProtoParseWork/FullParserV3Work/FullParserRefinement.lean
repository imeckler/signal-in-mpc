import ProtoParseWork.FullParserV3Work.FailedMessageScan
import ProtoParseWork.FullParserV3Work.ObservedSuccess
import ProtoParseWork.FullParserV3Work.TraceUniqueness
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3.Observed
open SignalMessageIntegration DispatcherIntegration
open LibSignalReference.Candidate.ProstSkipSlice LibSignalReference.Candidate.ProstSkipBuf
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

abbrev initialObserved (bytes : Slice U8) : State (BitVec 8) (BitVec 64) := ⟨initialOf bytes,⟨0,0⟩⟩

theorem initial_observed_parse (bytes : Slice U8) :
    finish Word64.concrete ByteAuth.concrete (scan bytes 0 bytes.length (initialObserved bytes)) =
      parse VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes) := by
  have hl : (contents bytes).length = bytes.length := List.length_map _
  simp only [scan,parse,hl,List.range_eq_range',Nat.sub_zero]
  rfl

/-- Full implementation observation for the actual extracted default merge,
starting from the explicit six-None record. Success retains exact EOF and all
Options; failure retains exact suffix, constructor/parameters, raw EOF-vs-active
status, live frames, canonical masks and every mutated Option. Only diagnostic
stack text is quotiented by statusView. No Message::decode/Default wrapper claim. -/
def ParserObservation (bytes : Slice U8) (result : Outcome) (observed : State (BitVec 8) (BitVec 64)) : Prop :=
  match result.1 with
  | .Ok () => ∃ hat : StateAt bytes bytes.length observed.parser [],
      result.2.2 = drop bytes bytes.length ∧ messageView bytes observed.parser.fields hat.fields_size = result.2.1 ∧
      observed.error = ⟨0,0⟩
  | .Err error => MessageRejected bytes result.2.2 error observed result.2.1

theorem trace_parser_observation (bytes : Slice U8) (hcap : bytes.length ≤ 512) {result : Outcome}
    (trace : MergeTrace ⟨100#u32⟩ emptyMessage bytes result) :
    ParserObservation bytes result (parse VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes)) := by
  rcases result with ⟨status,message,after⟩
  cases status with
  | Ok u =>
    cases u
    obtain ⟨hat,hrest,hview⟩ := successful_trace_parse bytes hcap trace rfl
    have hd : (ProtoParse.parseBody VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes)).depth = 0 := hat.frames.depth_eq
    have herr := successful_parse_error bytes hat.ok hd
    change ∃ hat : StateAt bytes bytes.length (parse VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes)).parser [],
      after = drop bytes bytes.length ∧ messageView bytes _ hat.fields_size = message ∧
      (parse VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes)).error = ⟨0,0⟩
    simp only [erase_parse]
    exact ⟨hat,hrest,hview,herr⟩
  | Err error =>
    have h := failed_message_scan trace error rfl bytes 0 (initialObserved bytes) (Nat.zero_le _) hcap (initial_at bytes) rfl (initial_view bytes)
    unfold MessageRejectedScan at h
    rw [initial_observed_parse] at h
    exact h

/-- Actual all-outcomes parser implementation theorem on contiguous bodies of
at most512 bytes, actual default recursion100 and six initial None fields.
Constructive totality supplies the complete actual trace; callers assume no
primitive correctness, finite skip derivation or successful parse. -/
theorem actual_parser_refinement (unused : ActualMessageDriver.prost.message.Message Message)
    (bytes : Slice U8) (hcap : bytes.length ≤ 512) :
    ∃ result : Outcome,
      ActualMessageDriver.prost.message.Message.merge.default (withDispatcher unused) driverBuf emptyMessage bytes = .ok (result.1,result.2.1) ∧
      MergeTrace ⟨100#u32⟩ emptyMessage bytes result ∧ IsSuffix bytes result.2.2 ∧
      ParserObservation bytes result (parse VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes)) := by
  obtain ⟨result,ht,hr,hs,_⟩ := actual_merge_observation unused emptyMessage bytes
  exact ⟨result,hr,ht,hs,trace_parser_observation bytes hcap ht⟩

#print axioms initial_observed_parse
#print axioms trace_parser_observation
#print axioms actual_parser_refinement
end FullParserV3.Observed
