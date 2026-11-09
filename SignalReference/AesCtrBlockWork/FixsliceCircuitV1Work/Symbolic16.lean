import AesCtrBlockWork.FixsliceCircuitV1Work.Layout
import AesCtrBlockWork.FixsliceCircuitV1Work.Projection16
namespace LibSignalReference.Candidate.FixsliceCircuitV1
open TlsMpc TlsMpc.Signal.AesLayout TlsMpc.Signal.AesLinear
open _root_.Std.Tactic.BVDecide
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

def symbolic16 (block : Fin 4) : Ops (BVExpr 16) where
 bits := ⟨.const 0,(fun a b=>BvConstruct.bin a .xor b),(fun a b=>BvConstruct.bin a .and b),BvConstruct.un .not⟩
 mask x m := BvConstruct.bin x .and (.const (project block m))
 bor x y := BvConstruct.bin x .or y
 rotate4 x n := BvConstruct.un (.rotateRight n.val) x
 left4 x n := .shiftLeft x (.const (BitVec.ofNat 4 n.val))
 right4 x n := .shiftRight x (.const (BitVec.ofNat 4 n.val))

theorem evaluationHom16 (block : Fin 4) (assign : BVExpr.Assignment) :
 Hom (symbolic16 block) (concrete16 block) (BVExpr.eval assign) := by
 constructor
 · constructor <;>intros <;>simp [symbolic16,concrete16,BVBinOp.eval,BVUnOp.eval]
 · intros; simp [symbolic16,concrete16,BVBinOp.eval]
 · intros; simp [symbolic16,concrete16,BVBinOp.eval]
 · intros; simp [symbolic16,concrete16,BVUnOp.eval]
 · intro x n
   simp [symbolic16,concrete16,BVExpr.eval_shiftLeft,BitVec.toNat_ofNat,Nat.mod_eq_of_lt n.isLt]
 · intro x n
   simp [symbolic16,concrete16,BVExpr.eval_shiftRight,BitVec.toNat_ofNat,Nat.mod_eq_of_lt n.isLt]

def packedProject (block : Fin 4) (word : BitVec 64) : BitVec 16 :=
 AesSbox.packValue ((List.range 8).map (fun i=>word.extractLsb' (4*(i+8)+block.val) 1)) ++
 AesSbox.packValue ((List.range 8).map (fun i=>word.extractLsb' (4*i+block.val) 1))

theorem packedProject_correct (block : Fin 4) (word : BitVec 64) : packedProject block word=project block word := by
 apply BitVec.eq_of_getLsbD_eq
 intro i hi
 rw [project_bit _ _ _ hi]
 interval_cases i <;>simp only [packedProject,AesSbox.packValue,BitVec.getLsbD_append] <;>simp

def projectExpr (block : Fin 4) (word : BVExpr 64) : BVExpr 16 :=
 BvConstruct.append
  (AesSbox.packExpr ((List.range 8).map (fun i=>BvConstruct.extract (4*(i+8)+block.val) 1 word)))
  (AesSbox.packExpr ((List.range 8).map (fun i=>BvConstruct.extract (4*i+block.val) 1 word)))

theorem projectExpr_correct (block : Fin 4) (word : BVExpr 64) (assign : BVExpr.Assignment) :
 (projectExpr block word).eval assign=project block (word.eval assign) := by
 simp only [projectExpr,BvConstruct.eval_append,AesSbox.packExpr_refines,List.map_map,Function.comp_def,BvConstruct.eval_extract]
 exact packedProject_correct block (word.eval assign)

theorem symbolic_state_correct16 (block : Fin 4) (keys : Nat→Words (BVExpr 16)) (words : Words (BVExpr 16))
 (assign : BVExpr.Assignment) :
 mapWords (BVExpr.eval assign) (encrypt (symbolic16 block) keys words)=
 encrypt (concrete16 block) (fun i=>mapWords (BVExpr.eval assign) (keys i)) (mapWords (BVExpr.eval assign) words) :=
 encrypt_map (evaluationHom16 block assign) keys words
end LibSignalReference.Candidate.FixsliceCircuitV1
