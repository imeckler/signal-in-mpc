import AesCtrBlockWork.FixsliceCircuitV1Work.Core
import TlsMpc.Signal.AesKeyInput
namespace LibSignalReference.Candidate.FixsliceCircuitV1
open TlsMpc TlsMpc.Signal.AesLayout TlsMpc.Signal.AesLinear
open _root_.Std.Tactic.BVDecide

def symbolic64 : Ops (BVExpr 64) where
 bits := TlsMpc.Signal.AesKeySchedule.wordExprOps
 mask x m := BvConstruct.bin x .and (.const m)
 bor x y := BvConstruct.bin x .or y
 rotate4 x n := BvConstruct.un (.rotateRight (4*n.val)) x
 left4 x n := .shiftLeft x (.const (BitVec.ofNat 6 (4*n.val)))
 right4 x n := .shiftRight x (.const (BitVec.ofNat 6 (4*n.val)))

theorem evaluationHom64 (assign : BVExpr.Assignment) : Hom symbolic64 concrete64 (BVExpr.eval assign) := by
 constructor
 · exact TlsMpc.Signal.AesKeySchedule.wordEvaluationHom assign
 · intros; simp [symbolic64,concrete64,BVBinOp.eval]
 · intros; simp [symbolic64,concrete64,BVBinOp.eval]
 · intros; simp [symbolic64,concrete64,BVUnOp.eval]
 · intro x n
   have hn : 4*n.val<64 := by omega
   simp [symbolic64,concrete64,BVExpr.eval_shiftLeft,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn]
 · intro x n
   have hn : 4*n.val<64 := by omega
   simp [symbolic64,concrete64,BVExpr.eval_shiftRight,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn]

theorem symbolic_state_correct (keys : Nat→Words (BVExpr 64)) (words : Words (BVExpr 64))
 (assign : BVExpr.Assignment) :
 mapWords (BVExpr.eval assign) (encrypt symbolic64 keys words) =
 encrypt concrete64 (fun i=>mapWords (BVExpr.eval assign) (keys i)) (mapWords (BVExpr.eval assign) words) :=
 encrypt_map (evaluationHom64 assign) keys words
end LibSignalReference.Candidate.FixsliceCircuitV1
