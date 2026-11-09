import ChatResponseReferenceWork.ParserCircuitCandidateV1.AdmissionStep
open TlsMpc TlsMpc.Signal Std.Tactic.BVDecide
namespace ChatResponseReference.ParserCircuitCandidateV1
set_option maxRecDepth 100000

section Mapping
variable {o : Word64.Ops B W} {o' : Word64.Ops C V}
  {a : ByteAuth.Ops B} {a' : ByteAuth.Ops C} {f : B → C} {fw : W → V}

theorem expand_admit_map (ha : ByteAuth.Hom a a' f) (raw : List B) :
    (expandAdmitInput a raw).map f = expandAdmitInput a' (raw.map f) := by
  simp only [expandAdmitInput,List.map_map]
  apply List.map_congr_left
  intro index member
  dsimp only [Function.comp_apply]
  cases source : expandedSourceIndex index with
  | none => exact ha.const 0
  | some position => exact TlsWebSocketUpgrade.get_map ha raw position

theorem compact_admit_map (ha : ByteAuth.Hom a a' f) (raw : List B) :
    (compactAdmitOutput a raw).map f = compactAdmitOutput a' (raw.map f) := by
  unfold compactAdmitOutput
  rw [List.map_take,compact_map ha]

theorem runAdmit_map (ho : Word64.Hom o o' f fw) (ha : ByteAuth.Hom a a' f) (raw : List B) :
    (runAdmit o a raw).map f = runAdmit o' a' (raw.map f) := by
  unfold runAdmit
  rw [compact_admit_map ha,TlsChatResponseMux.runAdmit_map ho ha,expand_admit_map ha]
end Mapping

theorem compiled_admit_correct (raw : List (BVExpr 8)) (assign : BVExpr.Assignment)
    (index : Nat) (bound : index < 8*(runAdmit Word64.symbolic ByteAuth.symbolic raw).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (runAdmit Word64.symbolic ByteAuth.symbolic raw))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (runAdmit Word64.symbolic ByteAuth.symbolic raw))).vec.get index bound)) =
    (ByteCircuit.joinValue (runAdmit Word64.concrete ByteAuth.concrete (raw.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,runAdmit_map (Word64.evaluationHom assign) (ByteAuth.evaluationHom assign)]

theorem compiled_encoded_admit (raw : List (BVExpr 8)) (assign : BVExpr.Assignment)
    (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64)) (shape : MuxCodecShape state)
    (slotIndex : BitVec 8) (id : BitVec 64) (valid : BitVec 8)
    (encoded : raw.map (BVExpr.eval assign) = encodeCompactAdmit state slotIndex id valid)
    (index : Nat) (bound : index < 8*(runAdmit Word64.symbolic ByteAuth.symbolic raw).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (runAdmit Word64.symbolic ByteAuth.symbolic raw))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (runAdmit Word64.symbolic ByteAuth.symbolic raw))).vec.get index bound)) =
    (ByteCircuit.joinValue (encodeCompactState
      (TlsChatResponseMux.admit Word64.concrete ByteAuth.concrete state slotIndex id valid))).getLsbD index := by
  rw [compiled_admit_correct raw assign index bound,encoded,encoded_admit_step state shape]

#print axioms runAdmit_map
#print axioms compiled_admit_correct
#print axioms compiled_encoded_admit
end ChatResponseReference.ParserCircuitCandidateV1
