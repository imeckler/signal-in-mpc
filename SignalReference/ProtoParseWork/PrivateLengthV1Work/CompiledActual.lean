import ProtoParseWork.PrivateLengthV1Work.Wire
import ProtoParseWork.PrivateLengthV1Work.ActualBody
import ProtoParseWork.FullParserV3Work.CompiledParserRefinement
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal Std.Tactic.BVDecide
namespace PrivateLengthV1.CompiledActual
open SignalMessageIntegration DispatcherIntegration FullParserV3 FullParserV3.Observed
open LibSignalReference.Candidate.ProstSkipSlice LibSignalReference.Candidate.ProstSkipBuf

/-- Existing production acceptance/metadata, with the computed upstream mask
checked canonically. Diagnostics remain in the proof observation only. -/
def projection (wire : List (BitVec 8)) (upstream : BitVec 8)
    (observed : FullParserV3.Observed.State (BitVec 8) (BitVec 64)) : List (BitVec 8) :=
  let accepted := ByteAuth.concrete.and
    (ByteAuth.eqMask ByteAuth.concrete upstream (ByteAuth.concrete.const 255))
    (ProtoParse.acceptedMask Word64.concrete ByteAuth.concrete wire observed.parser)
  accepted :: ByteAuth.release ByteAuth.concrete accepted
    (ProtoParse.metadata Word64.concrete ByteAuth.concrete wire observed.parser)

theorem upstream_rejection (wire : List (BitVec 8)) (upstream : BitVec 8)
    (observed : FullParserV3.Observed.State (BitVec 8) (BitVec 64)) (rejected : upstream ≠ 255) :
    projection wire upstream observed = List.replicate 90 0 := by
  have mask : ByteAuth.eqMask ByteAuth.concrete upstream (ByteAuth.concrete.const 255) = 0 := by
    rw [ByteAuth.eqMask_value]
    exact if_neg rejected
  unfold projection
  rw [mask]
  simp [ByteAuth.release,ByteAuth.concrete,List.map_const',ProtoParse.metadata_length]

/-- All-outcomes compiled private-length parser agreement with the accepted
actual pinned Rust default merge on that body slice. The logical length is
related to the assignment; it is never a public loop bound in production.

The inherited source boundary is explicit six-None initialization, recursion100,
contiguous bounded slice and successful bounded allocation/content models.
This does not claim MAC authentication, typed SignalMessage::decode wrappers,
receive-state security or the complete Signal session theorem. -/
theorem compiled_actual_private_parser (unused : ActualMessageDriver.prost.message.Message Message)
    (bytes : Slice U8) (wire : List (BVExpr 8)) (lengthHigh lengthLow upstream : BVExpr 8)
    (assign : BVExpr.Assignment) (length : Nat)
    (within : length ≤ wire.length) (capacity : wire.length ≤ 512)
    (high : BVExpr.eval assign lengthHigh = BitVec.ofNat 8 (length/256))
    (low : BVExpr.eval assign lengthLow = BitVec.ofNat 8 length)
    (body : ProtoParse.body ((wire.map (BVExpr.eval assign)).take length) = contents bytes) :
    ∃ result : Outcome, ∃ observed : FullParserV3.Observed.State (BitVec 8) (BitVec 64),
      ActualMessageDriver.prost.message.Message.merge.default
        (withDispatcher unused) driverBuf emptyMessage bytes = .ok (result.1,result.2.1) ∧
      MergeTrace ⟨100#u32⟩ emptyMessage bytes result ∧ IsSuffix bytes result.2.2 ∧
      ParserObservation bytes result observed ∧
      (PrivateProtoParseV1.parse VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
        (wire.map (BVExpr.eval assign)) (BVExpr.eval assign lengthHigh) (BVExpr.eval assign lengthLow)
        (BVExpr.eval assign upstream)).state = Stack.pad observed.parser
          (Wire.stackTail (wire.map (BVExpr.eval assign)) length) ∧
      ∀ index (inside : index < 8 * (PrivateProtoParseV1.parseCore VarintDecode.Spqr.symbolic
          Word64.symbolic ByteAuth.symbolic wire lengthHigh lengthLow upstream).length),
        PrivateProtoParseV1.compiledBit (PrivateProtoParseV1.parseCore VarintDecode.Spqr.symbolic
          Word64.symbolic ByteAuth.symbolic wire lengthHigh lengthLow upstream) assign index inside =
        (ByteCircuit.joinValue (projection ((wire.map (BVExpr.eval assign)).take length)
          (BVExpr.eval assign upstream) observed)).getLsbD index := by
  let concreteWire := wire.map (BVExpr.eval assign)
  have withinConcrete : length ≤ concreteWire.length := by simpa [concreteWire] using within
  have capacityConcrete : concreteWire.length ≤ 512 := by simpa [concreteWire] using capacity
  have nativeCapacity : bytes.length ≤ 512 := by
    have h := congrArg List.length body
    have contentLength : (contents bytes).length = bytes.length := List.length_map _
    rw [contentLength,Framing.body_length,List.length_take,List.length_map,Nat.min_eq_left within] at h
    omega
  obtain ⟨result,native,trace,suffix,observation⟩ := actual_parser_refinement unused bytes nativeCapacity
  let observed := FullParserV3.Observed.parse VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes)
  have erase : observed.parser = ProtoParse.parseBody VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      (ProtoParse.body (concreteWire.take length)) := by
    change (FullParserV3.Observed.parse VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      (contents bytes)).parser = _
    rw [FullParserV3.Observed.erase_parse,body]
  have state : (PrivateProtoParseV1.parse VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      (wire.map (BVExpr.eval assign)) (BVExpr.eval assign lengthHigh) (BVExpr.eval assign lengthLow)
      (BVExpr.eval assign upstream)).state = Stack.pad observed.parser (Wire.stackTail concreteWire length) := by
    rw [high,low,Wire.state_take concreteWire length (BVExpr.eval assign upstream) withinConcrete capacityConcrete,erase]
  have production : PrivateProtoParseV1.parseCore VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      (wire.map (BVExpr.eval assign)) (BVExpr.eval assign lengthHigh) (BVExpr.eval assign lengthLow)
      (BVExpr.eval assign upstream) = projection (concreteWire.take length) (BVExpr.eval assign upstream) observed := by
    rw [high,low,Wire.core_projection concreteWire length (BVExpr.eval assign upstream) withinConcrete capacityConcrete]
    unfold projection
    rw [erase]
  refine ⟨result,observed,native,trace,suffix,observation,state,?_⟩
  intro index inside
  exact (PrivateProtoParseV1.compiled_parseCore_correct wire lengthHigh lengthLow upstream assign index inside).trans
    (congrArg (fun output => (ByteCircuit.joinValue output).getLsbD index) production)

#print axioms upstream_rejection
#print axioms compiled_actual_private_parser
end PrivateLengthV1.CompiledActual
