import ChatResponseReferenceWork.ParserCircuitCandidateV1.EncodedByteStep
open TlsMpc TlsMpc.Signal Std.Tactic.BVDecide
namespace ChatResponseReference.ParserCircuitCandidateV1
set_option maxRecDepth 100000

theorem compiled_encoded_byte (capacity : Nat) (raw : List (BVExpr 8)) (assign : BVExpr.Assignment)
    (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64)) (shape : MuxCodecShape state)
    (safe : SafeStack state.parser) (active beginning ending byte : BitVec 8)
    (encoded : raw.map (BVExpr.eval assign) = encodeCompactInput state active beginning ending byte)
    (index : Nat) (bound : index < 8*(runByte VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic capacity raw).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (runByte VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic capacity raw))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (runByte VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic capacity raw))).vec.get index bound)) =
    (ByteCircuit.joinValue (compactEvent
      (TlsChatResponseMux.process VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
        capacity state active beginning ending byte))).getLsbD index := by
  rw [compiled_correct capacity raw assign index bound,encoded,encoded_byte_step capacity state shape safe]

#print axioms compiled_encoded_byte
end ChatResponseReference.ParserCircuitCandidateV1
