import TlsMpc.Signal.AesKeyColumns
import TlsMpc.Signal.AesShift

/-! Operations for compiling the actual portable AES256 key-schedule control
flow. These definitions use the existing S-box network in 64 parallel lanes. -/

namespace TlsMpc.Signal.AesKeySchedule

open Std.Tactic.BVDecide

structure Ops (W : Type) where
  zero : W
  xor : W → W → W
  not : W → W
  rcon : W
  substitute : List W → List W
  column : Nat → W → W → W
  inv1 : W → W
  inv2 : W → W
  inv3 : W → W

def wordOps : AesSbox.Ops (BitVec 64) := ⟨0, (· ^^^ ·), (· &&& ·), (~~~ ·)⟩

def wordExprOps : AesSbox.Ops (BVExpr 64) :=
  ⟨.const 0, (fun a b => BvConstruct.bin a .xor b),
    (fun a b => BvConstruct.bin a .and b), BvConstruct.un .not⟩

def wordEvaluationHom (assign : BVExpr.Assignment) :
    AesSbox.Hom wordExprOps wordOps (BVExpr.eval assign) := by
  constructor <;> intros <;> simp [wordExprOps, wordOps, BVBinOp.eval, BVUnOp.eval]

def deltaExpr (word : BVExpr 64) (shift : Fin 64) (mask : BitVec 64) : BVExpr 64 :=
  let amount := BVExpr.const (BitVec.ofNat 6 shift.val)
  let moved := BvConstruct.bin word .xor (.shiftRight word amount)
  let t := BvConstruct.bin moved .and (.const mask)
  BvConstruct.bin word .xor (BvConstruct.bin t .xor (.shiftLeft t amount))

theorem deltaExpr_refines (word : BVExpr 64) (shift : Fin 64) (mask : BitVec 64)
    (assign : BVExpr.Assignment) :
    (deltaExpr word shift mask).eval assign = AesLinear.deltaWord (word.eval assign) shift.val mask := by
  simp [deltaExpr, AesLinear.deltaWord, BVExpr.eval_shiftRight, BVExpr.eval_shiftLeft,
    BVBinOp.eval, BVExpr.eval_const]

def concrete : Ops (BitVec 64) where
  zero := 0
  xor := (· ^^^ ·)
  not := (~~~ ·)
  rcon := 0xf0000000
  substitute := AesSbox.circuit wordOps
  column := AesKeyColumns.column AesKeyColumns.concrete
  inv1 := AesLinear.shiftWord3
  inv2 := AesLinear.shiftWord2
  inv3 := AesLinear.shiftWord1

def symbolic : Ops (BVExpr 64) where
  zero := .const 0
  xor := fun a b => BvConstruct.bin a .xor b
  not := BvConstruct.un .not
  rcon := .const 0xf0000000
  substitute := AesSbox.circuit wordExprOps
  column := AesKeyColumns.column AesKeyColumns.symbolic
  inv1 := fun word => deltaExpr (deltaExpr word ⟨8,by decide⟩ 0x000f00ff00f00000)
      ⟨4,by decide⟩ 0x0f0f00000f0f0000
  inv2 := fun word => deltaExpr word ⟨8,by decide⟩ 0x00ff000000ff0000
  inv3 := fun word => deltaExpr (deltaExpr word ⟨8,by decide⟩ 0x00f000ff000f0000)
      ⟨4,by decide⟩ 0x0f0f00000f0f0000

structure Hom (a : Ops W) (b : Ops W') (f : W → W') : Prop where
  zero : f a.zero = b.zero
  xor : ∀ x y, f (a.xor x y) = b.xor (f x) (f y)
  not : ∀ x, f (a.not x) = b.not (f x)
  rcon : f a.rcon = b.rcon
  substitute : ∀ words, (a.substitute words).map f = b.substitute (words.map f)
  column : ∀ rotation x y, f (a.column rotation x y) = b.column rotation (f x) (f y)
  inv1 : ∀ x, f (a.inv1 x) = b.inv1 (f x)
  inv2 : ∀ x, f (a.inv2 x) = b.inv2 (f x)
  inv3 : ∀ x, f (a.inv3 x) = b.inv3 (f x)

def evaluationHom (assign : BVExpr.Assignment) : Hom symbolic concrete (BVExpr.eval assign) := by
  constructor
  · rfl
  · intros; simp [symbolic, concrete, BVBinOp.eval]
  · intro; simp [symbolic, concrete, BVUnOp.eval]
  · rfl
  · intro words; exact AesSbox.circuit_map (wordEvaluationHom assign) words
  · intro rotation x y; exact AesKeyColumns.column_refines rotation x y assign
  · intro; simp [symbolic, concrete, deltaExpr_refines, AesLinear.shiftWord3] <;> rfl
  · intro; simp [symbolic, concrete, deltaExpr_refines, AesLinear.shiftWord2] <;> rfl
  · intro; simp [symbolic, concrete, deltaExpr_refines, AesLinear.shiftWord1] <;> rfl

end TlsMpc.Signal.AesKeySchedule
