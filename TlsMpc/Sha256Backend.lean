import TlsMpc.Sha256ParallelPrefix

/-! Explicit circuit backend selection. Legacy defaults stay unchanged. -/
namespace TlsMpc.Sha256Backend
open Std.Tactic.BVDecide

inductive Profile where
  | reference
  | gateEfficient
  | latency
  deriving Repr,DecidableEq

def Profile.tag : Profile → String
  | .reference => "reference"
  | .gateEfficient => "gate-efficient"
  | .latency => "latency"

def Profile.parse : String → Option Profile
  | "reference" => some .reference
  | "gate-efficient" => some .gateEfficient
  | "latency" => some .latency
  | _ => none

def nary (o : Sha256.Ops B W) : Sha256.Ops B W :=
  {o with sum4:=Sha256CarrySave.sum4 o,sum5:=Sha256CarrySave.sum5 o}

def select (profile : Profile) (o : Sha256.Ops B W) : Sha256.Ops B W :=
  match profile with
  | .reference => o
  | .gateEfficient => nary o
  | .latency => nary (Sha256ParallelPrefix.prefixOps o)

theorem nary_concrete : nary Sha256.concrete=Sha256.concrete := by
  have h4 : Sha256CarrySave.sum4 Sha256.concrete=Sha256.concrete.sum4 :=
    funext fun a => funext fun b => funext fun c => funext fun d => Sha256CarrySave.sum4_correct a b c d
  have h5 : Sha256CarrySave.sum5 Sha256.concrete=Sha256.concrete.sum5 :=
    funext fun a => funext fun b => funext fun c => funext fun d => funext fun e => Sha256CarrySave.sum5_correct a b c d e
  unfold nary
  rw [h4,h5]

theorem select_concrete (profile : Profile) : select profile Sha256.concrete=Sha256.concrete := by
  cases profile
  · rfl
  · exact nary_concrete
  · change nary (Sha256ParallelPrefix.prefixOps Sha256.concrete)=Sha256.concrete
    rw [Sha256ParallelPrefix.prefixOps_concrete,nary_concrete]

theorem nary_map {o : Sha256.Ops B W} {o' : Sha256.Ops B' W'} {fb : B → B'} {fw : W → W'}
    (hom : Sha256.Hom o o' fb fw) : Sha256.Hom (nary o) (nary o') fb fw :=
  {hom with sum4:=Sha256CarrySave.sum4_map hom,sum5:=Sha256CarrySave.sum5_map hom}

theorem select_map (profile : Profile) {o : Sha256.Ops B W} {o' : Sha256.Ops B' W'} {fb : B → B'} {fw : W → W'}
    (hom : Sha256.Hom o o' fb fw) : Sha256.Hom (select profile o) (select profile o') fb fw := by
  cases profile
  · exact hom
  · exact nary_map hom
  · exact nary_map (Sha256ParallelPrefix.prefixOps_map hom)

def evaluationHom (profile : Profile) (assign : BVExpr.Assignment) :
    Sha256.Hom (select profile Sha256.symbolic) Sha256.concrete (BVExpr.eval assign) (BVExpr.eval assign) := by
  have h:=select_map profile (Sha256.evaluationHom assign)
  rw [select_concrete] at h
  exact h

theorem compiled_compress_correct (profile : Profile) (state : Sha256.State (BVExpr 32))
    (block : List (BVExpr 32)) (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8*(Sha256.digest Sha256.symbolic (Sha256.compress (select profile Sha256.symbolic) state block)).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (Sha256.digest Sha256.symbolic (Sha256.compress (select profile Sha256.symbolic) state block)))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (Sha256.digest Sha256.symbolic (Sha256.compress (select profile Sha256.symbolic) state block)))).vec.get index hi)) =
    (ByteCircuit.joinValue (Sha256.digest Sha256.concrete (Sha256.compress Sha256.concrete
      (state.map (BVExpr.eval assign)) (block.map (BVExpr.eval assign))))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,Sha256.digest_map (Sha256.evaluationHom assign),
    Sha256.compress_map (evaluationHom profile assign)]

end TlsMpc.Sha256Backend
