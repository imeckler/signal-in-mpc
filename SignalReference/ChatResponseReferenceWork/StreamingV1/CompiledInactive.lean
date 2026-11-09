import ChatResponseReferenceWork.StreamingV1.InactiveByte
open TlsMpc TlsMpc.Signal
open Std.Tactic.BVDecide
namespace ChatResponseReference.StreamingV1

/-- Existing production AIG compiler endpoint composed with actual inactive-byte
state/event preservation. The raw-state and private-control hypotheses are
explicit; this does not assert the complete response source relation. -/
theorem compiled_inactive_correct (capacity : Nat) (raw : List (BVExpr 8)) (assign : BVExpr.Assignment)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (shape : StateShape state)
    (decoded : TlsChatResponse.readState Word64.concrete ByteAuth.concrete
      ((raw.map (BVExpr.eval assign)).take TlsChatResponse.stateSize) = state)
    (active : TlsWebSocketUpgrade.get ByteAuth.concrete (raw.map (BVExpr.eval assign)) TlsChatResponse.stateSize = 0)
    (beginning : TlsWebSocketUpgrade.get ByteAuth.concrete (raw.map (BVExpr.eval assign)) (TlsChatResponse.stateSize+1) = 0)
    (ending : TlsWebSocketUpgrade.get ByteAuth.concrete (raw.map (BVExpr.eval assign)) (TlsChatResponse.stateSize+2) = 0)
    (index : Nat) (bound : index < 8*(TlsChatResponse.runByte VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic capacity raw).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (TlsChatResponse.runByte VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic capacity raw))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (TlsChatResponse.runByte VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic capacity raw))).vec.get index bound)) =
      (ByteCircuit.joinValue ([state.valid,state.finished,state.successful,0,0,0] ++
        TlsChatResponse.stateBytes Word64.concrete state)).getLsbD index := by
  rw [TlsChatResponse.compiled_runByte_correct capacity raw assign index bound]
  rw [runByte_inactive capacity state (raw.map (BVExpr.eval assign)) shape decoded active beginning ending]

#print axioms compiled_inactive_correct
end ChatResponseReference.StreamingV1
