import ProtoParseWork.FullParserV3Work.ObservedSuccess
import ProtoParseWork.FullParserV3Work.ObservedCircuit
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal Std.Tactic.BVDecide
namespace FullParserV3.Observed
open LibSignalReference.Candidate.ProstSkipSlice ParserErrorStateV2
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

/-- Complete private successful observation, retaining all six unmasked records.
The records are related to actual Rust Options by messageView; scalar projection
explicitly truncates raw uint64 metadata, and bytes offsets denote original body
content. This is proof instrumentation, not a production diagnostic export. -/
def successBytes (state : ProtoParse.State (BitVec 8) (BitVec 64)) : List (BitVec 8) :=
  255 :: (Word64.bytes Word64.concrete state.next ++ Word64.bytes Word64.concrete 0 ++
    Word64.bytes Word64.concrete 0 ++ (List.range 6).flatMap (fieldBytes Word64.concrete ByteAuth.concrete state))

theorem view_actual_success (unused : ActualMessageDriver.prost.message.Message Message)
    (bytes : Slice U8) (message : Message) (hcap : bytes.length ≤ 512)
    (hactual : ActualMessageDriver.prost.message.Message.merge.default (withDispatcher unused) driverBuf emptyMessage bytes = .ok (.Ok (),message)) :
    ∃ state, ∃ hat : StateAt bytes bytes.length state [], messageView bytes state.fields hat.fields_size = message ∧
      viewCore VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes) = successBytes state := by
  let observed := parse VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes)
  have h : ∃ hat : StateAt bytes bytes.length observed.parser [],
      messageView bytes observed.parser.fields hat.fields_size = message ∧ observed.error = ⟨0,0⟩ :=
    actual_successful_observation unused bytes message hcap hactual
  obtain ⟨hat,hview,herr⟩ := h
  refine ⟨observed.parser,hat,hview,?_⟩
  have hn : Word64.eq Word64.concrete ByteAuth.concrete observed.parser.next (Word64.concrete.const bytes.length) = 255 := by
    rw [hat.cursor]; exact word_eq_self _
  have hd : Word64.eq Word64.concrete ByteAuth.concrete observed.parser.depth (Word64.concrete.const 0) = 255 := by
    rw [hat.frames.depth_eq]; exact word_eq_self _
  have hcomplete : ProtoParse.completeMask Word64.concrete ByteAuth.concrete bytes.length observed.parser = 255 := by
    simp only [ProtoParse.completeMask,hat.ok,hn,hd]
    rfl
  have hl : (contents bytes).length = bytes.length := List.length_map _
  unfold viewCore
  change ProtoParse.completeMask Word64.concrete ByteAuth.concrete (contents bytes).length observed.parser ::
    (Word64.bytes Word64.concrete observed.parser.next ++ Word64.bytes Word64.concrete observed.error.code ++
      Word64.bytes Word64.concrete observed.error.parameter ++ (List.range 6).flatMap
        (fieldBytes Word64.concrete ByteAuth.concrete observed.parser)) = successBytes observed.parser
  rw [hl,hcomplete,herr]
  rfl

/-- Actual circuit-to-extracted-parser implementation theorem for successful
bounded inputs. Rejection remains an explicit separate unfinished obligation. -/
theorem compiled_actual_success (unused : ActualMessageDriver.prost.message.Message Message)
    (bytes : Slice U8) (message : Message) (hcap : bytes.length ≤ 512)
    (hactual : ActualMessageDriver.prost.message.Message.merge.default (withDispatcher unused) driverBuf emptyMessage bytes = .ok (.Ok (),message))
    (secret : List (BVExpr 8)) (assign : BVExpr.Assignment) (hinput : secret.map (BVExpr.eval assign) = contents bytes) :
    ∃ state, ∃ hat : StateAt bytes bytes.length state [], messageView bytes state.fields hat.fields_size = message ∧
      ∀ index (hi : index < 8 * (viewCore VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic secret).length),
      AigExport.evalRef
        (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
          (viewCore VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic secret))).aig)
        (fun varId bit => (assign.get varId).bv.getLsbD bit)
        (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
          (viewCore VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic secret))).vec.get index hi)) =
        (ByteCircuit.joinValue (successBytes state)).getLsbD index := by
  obtain ⟨state,hat,hview,hbytes⟩ := view_actual_success unused bytes message hcap hactual
  refine ⟨state,hat,hview,?_⟩
  intro index hi
  rw [compiled_viewCore_correct secret assign index hi,hinput,hbytes]

#print axioms view_actual_success
#print axioms compiled_actual_success
end FullParserV3.Observed
