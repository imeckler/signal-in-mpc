import ProtoParseWork.PrivateLengthV1Work.Scan
import ProtoParseWork.FullParserV3Work.FullParserRefinement
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace PrivateLengthV1.ActualBody
open SignalMessageIntegration DispatcherIntegration FullParserV3 FullParserV3.Observed
open LibSignalReference.Candidate.ProstSkipSlice LibSignalReference.Candidate.ProstSkipBuf

/-- Instantiate the accepted all-outcomes actual Rust default-merge theorem
on the private prefix. Native suffix, error constructor/parameters and mutated
Options are retained by ParserObservation. The production private parser adds
only a zero stack tail; it does not assume primitive or message correctness. -/
theorem actual_private_body (unused : ActualMessageDriver.prost.message.Message Message)
    (bytes : Slice U8) (capacityBytes : List (BitVec 8)) (ending : Nat)
    (within : ending ≤ capacityBytes.length) (capacity : capacityBytes.length ≤ 512)
    (prefixContents : contents bytes = capacityBytes.take ending) :
    ∃ result : Outcome, ∃ observed : FullParserV3.Observed.State (BitVec 8) (BitVec 64),
      ActualMessageDriver.prost.message.Message.merge.default
        (withDispatcher unused) driverBuf emptyMessage bytes = .ok (result.1,result.2.1) ∧
      MergeTrace ⟨100#u32⟩ emptyMessage bytes result ∧ IsSuffix bytes result.2.2 ∧
      ParserObservation bytes result observed ∧
      PrivateProtoParseV1.parseBody VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
        (BitVec.ofNat 64 ending) capacityBytes = Stack.pad observed.parser
          (min 100 capacityBytes.length-min 100 ending) := by
  have length : bytes.length = ending := by
    have h := congrArg List.length prefixContents
    have contentLength : (contents bytes).length = bytes.length := List.length_map _
    rw [contentLength,List.length_take,Nat.min_eq_left within] at h
    exact h
  obtain ⟨result,native,trace,suffix,observation⟩ := actual_parser_refinement unused bytes (by omega)
  refine ⟨result,FullParserV3.Observed.parse VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
    (contents bytes),native,trace,suffix,observation,?_⟩
  rw [Scan.parseBody_take capacityBytes ending within capacity,FullParserV3.Observed.erase_parse,prefixContents]

#print axioms actual_private_body
end PrivateLengthV1.ActualBody
