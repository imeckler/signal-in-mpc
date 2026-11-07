import TlsMpc.Signal.MlKemPke
namespace TlsMpc.Signal.MlKemPoly
open Std.Tactic.BVDecide

def run (r : MlKemArithmetic.Ops W) (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (subtract : Bool) (raw : List B) : List B :=
  let x := MlKemNtt.decodePoly s a (raw.take 512)
  let y := MlKemNtt.decodePoly s a (raw.drop 512)
  MlKemNtt.encodePoly s (if subtract then MlKemPke.sub r s x y else MlKemPke.add r s x y)

theorem run_map {r : MlKemArithmetic.Ops W} {r' : MlKemArithmetic.Ops W'}
    {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
    {f : B → B'} {g : W → W'} (hr : MlKemArithmetic.Hom r r' g) (hs : Sha256.Hom s s' f g) (ha : ByteAuth.Hom a a' f)
    (subtract : Bool) (raw : List B) : (run r s a subtract raw).map f = run r' s' a' subtract (raw.map f) := by
  cases subtract <;> simp only [run,Bool.false_eq_true,↓reduceIte,MlKemNtt.encodePoly_map hs,
    MlKemPke.add_map hr hs,MlKemPke.sub_map hr hs,MlKemNtt.decodePoly_map hs ha,List.map_take,List.map_drop]

theorem compiled_run_correct (subtract : Bool) (raw : List (BVExpr 8)) (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8*(run MlKemArithmetic.symbolic Sha256.symbolic ByteAuth.symbolic subtract raw).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (run MlKemArithmetic.symbolic Sha256.symbolic ByteAuth.symbolic subtract raw))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (run MlKemArithmetic.symbolic Sha256.symbolic ByteAuth.symbolic subtract raw))).vec.get index hi)) =
      (ByteCircuit.joinValue (run MlKemArithmetic.concrete Sha256.concrete ByteAuth.concrete subtract (raw.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,run_map (MlKemArithmetic.evaluationHom assign) (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]
end TlsMpc.Signal.MlKemPoly
