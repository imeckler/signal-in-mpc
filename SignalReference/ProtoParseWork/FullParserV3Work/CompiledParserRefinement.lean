import ProtoParseWork.FullParserV3Work.FullParserRefinement
import ProtoParseWork.FullParserV3Work.ObservedCircuit
import TlsMpc.Signal.ProtoParseProofs
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal Std.Tactic.BVDecide
namespace FullParserV3.Observed
open SignalMessageIntegration DispatcherIntegration
open LibSignalReference.Candidate.ProstSkipSlice LibSignalReference.Candidate.ProstSkipBuf
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

def observationBytes (capacity : Nat) (state : State (BitVec 8) (BitVec 64)) : List (BitVec 8) :=
  ProtoParse.completeMask Word64.concrete ByteAuth.concrete capacity state.parser ::
    (Word64.bytes Word64.concrete state.parser.next ++ Word64.bytes Word64.concrete state.error.code ++
      Word64.bytes Word64.concrete state.error.parameter ++ (List.range 6).flatMap (fieldBytes Word64.concrete ByteAuth.concrete state.parser))

/-- Unchanged production policy/projection: framing/version and mandatory
ratchet/counter/ciphertext checks, ratchet size/prefix checks, then masked
metadata. Diagnostics are proof-only and absent from this expression. -/
def productionProjection (wire : List (BitVec 8)) (state : State (BitVec 8) (BitVec 64)) : List (BitVec 8) :=
  let accepted := ProtoParse.acceptedMask Word64.concrete ByteAuth.concrete wire state.parser
  accepted :: ByteAuth.release ByteAuth.concrete accepted (ProtoParse.metadata Word64.concrete ByteAuth.concrete wire state.parser)

theorem production_erasure (wire : List (BitVec 8)) (bytes : Slice U8)
    (hbody : ProtoParse.body wire = contents bytes) :
    ProtoParse.parseCore VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete wire =
      productionProjection wire (parse VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes)) := by
  rw [←hbody]
  exact (erase_external VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete wire).symm

/-- The existing checked API has the same projection; its public wire-size
bound remains512, separately from the body bound in actual_parser_refinement. -/
theorem production_checked_erasure (wire : List (BitVec 8)) (bytes : Slice U8)
    (hw : wire.length ≤ 512) (hbody : ProtoParse.body wire = contents bytes) :
    ProtoParse.parseChecked VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete wire =
      some (productionProjection wire (parse VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes))) := by
  rw [ProtoParse.parseChecked,if_pos hw,production_erasure wire bytes hbody]

/-- Every actual rejection masks every production metadata byte. The complete
failed record still participates in ParserObservation; it is never called success. -/
theorem production_rejection (wire : List (BitVec 8)) (bytes after : Slice U8)
    (error : prost.error.DecodeError) (state : State (BitVec 8) (BitVec 64)) (message : Message)
    (hbody : ProtoParse.body wire = contents bytes) (h : MessageRejected bytes after error state message) :
    productionProjection wire state = 0 :: List.replicate
      (ProtoParse.metadata Word64.concrete ByteAuth.concrete wire state.parser).length 0 := by
  have hl : (contents bytes).length = bytes.length := List.length_map _
  have hc : ProtoParse.completeMask Word64.concrete ByteAuth.concrete (ProtoParse.body wire).length state.parser = 0 := by
    rw [hbody,hl]; exact h.observation.complete
  have ha : ProtoParse.acceptedMask Word64.concrete ByteAuth.concrete wire state.parser = 0 := by
    have hz (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
    have hz' (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
    simp only [ProtoParse.acceptedMask,hc,hz,hz']
  simp only [productionProjection,ha,ByteAuth.release_reject]

/-- Concrete production rejection follows from the actual Rust error return;
no successful parse or error-classification assumption is supplied by the caller. -/
theorem actual_rejection_is_masked (unused : ActualMessageDriver.prost.message.Message Message)
    (wire : List (BitVec 8)) (bytes : Slice U8) (hcap : bytes.length ≤ 512)
    (hbody : ProtoParse.body wire = contents bytes) (error : prost.error.DecodeError) (message : Message)
    (hactual : ActualMessageDriver.prost.message.Message.merge.default (withDispatcher unused) driverBuf emptyMessage bytes = .ok (.Err error,message)) :
    ProtoParse.parseCore VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete wire =
      0 :: List.replicate (ProtoParse.metadata Word64.concrete ByteAuth.concrete wire
        (parse VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes)).parser).length 0 := by
  obtain ⟨result,hr,ht,hs,ho⟩ := actual_parser_refinement unused bytes hcap
  rw [hactual] at hr
  have hstatus : result.1 = .Err error := (congrArg Prod.fst (Result.ok.inj hr)).symm
  have hf : MessageRejected bytes result.2.2 error
      (parse VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes)) result.2.1 := by
    simpa only [ParserObservation,hstatus] using ho
  rw [production_erasure wire bytes hbody]
  exact production_rejection wire bytes result.2.2 error _ result.2.1 hbody hf

/-- Private diagnostic circuit agrees with the actual parser on every outcome,
including malformed/duplicate/unknown/group cases. Its extra output is proof
instrumentation and is not added to production circuits. -/
theorem compiled_actual_parser (unused : ActualMessageDriver.prost.message.Message Message)
    (bytes : Slice U8) (hcap : bytes.length ≤ 512) (secret : List (BVExpr 8)) (assign : BVExpr.Assignment)
    (hinput : secret.map (BVExpr.eval assign) = contents bytes) :
    ∃ result : Outcome, ∃ state : State (BitVec 8) (BitVec 64),
      ActualMessageDriver.prost.message.Message.merge.default (withDispatcher unused) driverBuf emptyMessage bytes = .ok (result.1,result.2.1) ∧
      MergeTrace ⟨100#u32⟩ emptyMessage bytes result ∧ IsSuffix bytes result.2.2 ∧ ParserObservation bytes result state ∧
      ∀ index (hi : index < 8 * (viewCore VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic secret).length),
        AigExport.evalRef
          (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
            (viewCore VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic secret))).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
            (viewCore VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic secret))).vec.get index hi)) =
          (ByteCircuit.joinValue (observationBytes bytes.length state)).getLsbD index := by
  obtain ⟨result,hr,ht,hs,ho⟩ := actual_parser_refinement unused bytes hcap
  refine ⟨result,parse VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes),hr,ht,hs,ho,?_⟩
  intro index hi
  rw [compiled_viewCore_correct secret assign index hi,hinput]
  have hl : (contents bytes).length = bytes.length := List.length_map _
  unfold viewCore observationBytes
  rw [hl]

/-- Actual production circuit→parser implementation theorem. The compiled
circuit remains the existing ProtoParse.parseCore: only its existing policy and
masked metadata are emitted. Full native success/error observations accompany
the witness state, and production_rejection proves failed records are masked. -/
theorem compiled_actual_production_parser (unused : ActualMessageDriver.prost.message.Message Message)
    (bytes : Slice U8) (hcap : bytes.length ≤ 512) (wire : List (BVExpr 8)) (assign : BVExpr.Assignment)
    (hbody : ProtoParse.body (wire.map (BVExpr.eval assign)) = contents bytes) :
    ∃ result : Outcome, ∃ state : State (BitVec 8) (BitVec 64),
      ActualMessageDriver.prost.message.Message.merge.default (withDispatcher unused) driverBuf emptyMessage bytes = .ok (result.1,result.2.1) ∧
      MergeTrace ⟨100#u32⟩ emptyMessage bytes result ∧ IsSuffix bytes result.2.2 ∧ ParserObservation bytes result state ∧
      ∀ index (hi : index < 8 * (ProtoParse.parseCore VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic wire).length),
        AigExport.evalRef
          (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
            (ProtoParse.parseCore VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic wire))).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
            (ProtoParse.parseCore VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic wire))).vec.get index hi)) =
          (ByteCircuit.joinValue (productionProjection (wire.map (BVExpr.eval assign)) state)).getLsbD index := by
  obtain ⟨result,hr,ht,hs,ho⟩ := actual_parser_refinement unused bytes hcap
  refine ⟨result,parse VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes),hr,ht,hs,ho,?_⟩
  intro index hi
  rw [ProtoParse.compiled_parseCore_correct wire assign index hi,production_erasure _ bytes hbody]

#print axioms production_erasure
#print axioms production_checked_erasure
#print axioms production_rejection
#print axioms actual_rejection_is_masked
#print axioms compiled_actual_parser
#print axioms compiled_actual_production_parser
end FullParserV3.Observed
