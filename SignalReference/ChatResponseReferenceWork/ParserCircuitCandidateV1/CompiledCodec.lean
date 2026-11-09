import ChatResponseReferenceWork.ParserCircuitCandidateV1.Stack32Codec
open TlsMpc TlsMpc.Signal Std.Tactic.BVDecide
namespace ChatResponseReference.ParserCircuitCandidateV1
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
section Mapping
variable {B C W V : Type} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops C}
  {d : VarintDecode.Spqr.Ops B W} {d' : VarintDecode.Spqr.Ops C V}
  {o : Word64.Ops B W} {o' : Word64.Ops C V} {f : B → C} {fw : W → V}
  (ha : ByteAuth.Hom a a' f)
include ha

theorem compact_map (full : List B) :
    (compactOutput a full).map f = compactOutput a' (full.map f) := by
  simp only [compactOutput,List.map_map,Function.comp_apply]
  apply List.map_congr_left
  intro index member
  dsimp only [Function.comp_apply]
  exact TlsWebSocketUpgrade.get_map ha full (retainedIndex index)

theorem expand_map (raw : List B) :
    (expandInput a raw).map f = expandInput a' (raw.map f) := by
  simp only [expandInput,List.map_map,Function.comp_apply]
  apply List.map_congr_left
  intro index member
  dsimp only [Function.comp_apply]
  by_cases first : index < 73
  · simp only [if_pos first,TlsWebSocketUpgrade.get_map ha]
  · by_cases stack : index < 873
    · by_cases high : (index-73)%8 < 4
      · simp only [if_neg first,if_pos stack,if_pos high,ha.const]
      · simp only [if_neg first,if_pos stack,if_neg high,TlsWebSocketUpgrade.get_map ha]
    · simp only [if_neg first,if_neg stack,TlsWebSocketUpgrade.get_map ha]

theorem runByte_map (hd : VarintDecode.Spqr.Hom d d' f fw) (ho : Word64.Hom o o' f fw)
    (capacity : Nat) (raw : List B) :
    (runByte d o a capacity raw).map f = runByte d' o' a' capacity (raw.map f) := by
  unfold runByte
  rw [compact_map ha,TlsChatResponseMux.runByte_map hd ho ha,expand_map ha]
end Mapping

theorem compiled_correct (capacity : Nat) (raw : List (BVExpr 8)) (assign : BVExpr.Assignment)
    (index : Nat) (bound : index < 8*(runByte VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic capacity raw).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (runByte VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic capacity raw))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (runByte VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic capacity raw))).vec.get index bound)) =
      (ByteCircuit.joinValue (runByte VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete capacity
        (raw.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,runByte_map (ByteAuth.evaluationHom assign)
    (VarintDecode.Spqr.evaluationHom assign) (Word64.evaluationHom assign)]

#print axioms compact_map
#print axioms expand_map
#print axioms runByte_map
#print axioms compiled_correct
end ChatResponseReference.ParserCircuitCandidateV1
