import CtrReferenceV1Work.FixedGeneratorV1Work.Circuit
namespace LibSignalReference.Candidate.FixedCtr
open Aeneas Aeneas.Std TlsMpc
open _root_.Std.Tactic.BVDecide
open LibSignalReference.Candidate.FixsliceCircuitV1
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

theorem stream_expression_length (keys : Nat → TlsMpc.Signal.AesLayout.Words (BVExpr 64))
 (counter : U32) : (streamExpression keys counter).length = 16 := by
 simp [streamExpression,expression16]

theorem keystream_expression_length (keys : Nat → TlsMpc.Signal.AesLayout.Words (BVExpr 64))
 (n : Nat) (counter : U32) : (keystreamExpression keys n counter).length = 16*n := by
 induction n generalizing counter with
 | zero => simp [keystreamExpression,after]
 | succ n ih => simp only [keystreamExpression,List.length_append,stream_expression_length,ih]; omega

theorem keystream_append (keys : Nat → TlsMpc.Signal.AesLayout.Words (BVExpr 64))
 (a b : Nat) (counter : U32) :
 keystreamExpression keys (a+b) counter =
 keystreamExpression keys a counter ++ keystreamExpression keys b (after a counter) := by
 induction a generalizing counter with
 | zero => simp [keystreamExpression,after]
 | succ a ih =>
   simp only [Nat.succ_add,keystreamExpression,ih,after,List.append_assoc]

theorem keystream_take_blocks (keys : Nat → TlsMpc.Signal.AesLayout.Words (BVExpr 64))
 (a b : Nat) (counter : U32) (bounded : a ≤ b) :
 (keystreamExpression keys b counter).take (16*a) = keystreamExpression keys a counter := by
 have hb : b = a+(b-a) := by omega
 rw [hb,keystream_append,List.take_append,keystream_expression_length]
 simp only [Nat.sub_self,List.take_zero,List.append_nil]
 rw [←keystream_expression_length keys a counter,List.take_length]

theorem keystream_take_bytes (keys : Nat → TlsMpc.Signal.AesLayout.Words (BVExpr 64))
 (small large : Nat) (counter : U32) (bounded : small ≤ large) :
 (keystreamExpression keys ((large+15)/16) counter).take small =
 (keystreamExpression keys ((small+15)/16) counter).take small := by
 have hc : (small+15)/16 ≤ (large+15)/16 := by omega
 have hsize : small ≤ 16*((small+15)/16) := by omega
 rw [←keystream_take_blocks keys ((small+15)/16) ((large+15)/16) counter hc]
 simp only [List.take_take,Nat.min_eq_left hsize]

theorem zip_take_right {A B C : Type} (f : A → B → C) (xs : List A) (ys : List B)
 (n : Nat) (bounded : xs.length ≤ n) :
 List.zipWith f xs (ys.take n) = List.zipWith f xs ys := by
 induction xs generalizing ys n with
 | nil => rfl
 | cons a xs ih =>
   cases n with
   | zero => simp at bounded
   | succ n =>
     have hb : xs.length ≤ n := by simpa using bounded
     cases ys with
     | nil => rfl
     | cons b ys => simpa using congrArg (List.cons (f a b)) (ih ys n hb)

/-- Complete capacity ciphertext can be computed once, then privately truncated without
using padding bytes. No extra AES computation per candidate private length is needed. -/
theorem fresh_prefix (key : Nat → BVExpr 8) (input : List (BVExpr 8))
 (n : Nat) (bounded : n ≤ input.length) :
 (freshExpression key input).take n = freshExpression key (input.take n) := by
 have hlen : (input.take n).length = n := by simp [Nat.min_eq_left bounded]
 simp only [freshExpression,xorExpression,List.take_zipWith,hlen]
 rw [keystream_take_bytes _ n input.length _ bounded]
 exact zip_take_right _ _ _ n (by rw [hlen])

theorem fresh_prefix_evaluation (key : Nat → BVExpr 8) (input : List (BVExpr 8))
 (n : Nat) (bounded : n ≤ input.length) (assign : BVExpr.Assignment) :
 ((freshExpression key input).map (BVExpr.eval assign)).take n =
 (freshExpression key (input.take n)).map (BVExpr.eval assign) := by
 rw [←List.map_take,fresh_prefix key input n bounded]

end LibSignalReference.Candidate.FixedCtr
