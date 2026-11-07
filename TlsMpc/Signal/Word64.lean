import TlsMpc.Signal.Varint64

/-! Shared 64-bit cursor arithmetic. Comparisons use a 65-bit subtraction,
so unsigned bounds checks do not silently wrap at the word boundary. -/
namespace TlsMpc.Signal.Word64
open Std.Tactic.BVDecide

structure Ops (B W : Type) where
  const : Nat → W
  pack : List B → W
  unpack : W → Nat → B
  add : W → W → W
  sub : W → W → W
  shift : W → Nat → W
  band : W → W → W
  ule : W → W → B
  select : B → W → W → W

def concrete : Ops (BitVec 8) (BitVec 64) where
  const := BitVec.ofNat 64
  pack := Varint64.pack Varint64.concrete ByteAuth.concrete
  unpack x i := x.extractLsb' (8 * (7 - i)) 8
  add := (· + ·)
  sub := (· - ·)
  shift := (· >>> ·)
  band := (· &&& ·)
  ule x y := ~~~(BitVec.replicate 8 (((0#1 ++ y) - (0#1 ++ x)).extractLsb' 64 1))
  select mask x y :=
    let m := BitVec.replicate 8 mask
    (m &&& x) ^^^ ((~~~m) &&& y)

def subtract (x y : BVExpr n) : BVExpr n :=
  BvConstruct.bin x .add (BvConstruct.bin (BvConstruct.un .not y) .add (.const 1))

@[simp] theorem eval_subtract (assign : BVExpr.Assignment) (x y : BVExpr n) :
    BVExpr.eval assign (subtract x y) = BVExpr.eval assign x - BVExpr.eval assign y := by
  simp [subtract, BitVec.sub_eq_add_neg, BitVec.neg_eq_not_add]

def symbolic : Ops (BVExpr 8) (BVExpr 64) where
  const n := .const (BitVec.ofNat 64 n)
  pack := Varint64.pack Varint64.symbolic ByteAuth.symbolic
  unpack x i := BvConstruct.extract (8 * (7 - i)) 8 x
  add x y := BvConstruct.bin x .add y
  sub := subtract
  shift x i := .shiftRight x (.const (BitVec.ofNat (i + 1) i))
  band x y := BvConstruct.bin x .and y
  ule x y := BvConstruct.un .not (.replicate 8
    (BvConstruct.extract 64 1 (subtract (BvConstruct.append (.const 0#1) y)
      (BvConstruct.append (.const 0#1) x))) rfl)
  select mask x y :=
    let m : BVExpr 64 := .replicate 8 mask rfl
    BvConstruct.bin (BvConstruct.bin m .and x) .xor (BvConstruct.bin (BvConstruct.un .not m) .and y)

structure Hom (o : Ops B W) (o' : Ops B' W') (f : B → B') (fw : W → W') : Prop where
  const : ∀ n, fw (o.const n) = o'.const n
  pack : ∀ bytes, fw (o.pack bytes) = o'.pack (bytes.map f)
  unpack : ∀ x i, f (o.unpack x i) = o'.unpack (fw x) i
  add : ∀ x y, fw (o.add x y) = o'.add (fw x) (fw y)
  sub : ∀ x y, fw (o.sub x y) = o'.sub (fw x) (fw y)
  shift : ∀ x i, fw (o.shift x i) = o'.shift (fw x) i
  band : ∀ x y, fw (o.band x y) = o'.band (fw x) (fw y)
  ule : ∀ x y, f (o.ule x y) = o'.ule (fw x) (fw y)
  select : ∀ mask x y, fw (o.select mask x y) = o'.select (f mask) (fw x) (fw y)

def evaluationHom (assign : BVExpr.Assignment) :
    Hom symbolic concrete (BVExpr.eval assign) (BVExpr.eval assign) := by
  constructor
  · intro n; rfl
  · intro bytes; exact Varint64.pack_map (Varint64.evaluationHom assign) (ByteAuth.evaluationHom assign) bytes
  · intros; simp [symbolic, concrete]
  · intros; simp [symbolic, concrete]
  · intros; simp [symbolic, concrete]
  · intro x i
    have hi : i < 2 ^ (i + 1) := Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_pow_self (by decide))
    simp [symbolic, concrete, BVExpr.eval_shiftRight, Nat.mod_eq_of_lt hi]
  · intros; simp [symbolic, concrete]
  · intros; simp [symbolic, concrete, BVExpr.eval_replicate]
  · intros; simp [symbolic, concrete, BVExpr.eval_replicate]

def bytes (o : Ops B W) (word : W) : List B := (List.range 8).map (o.unpack word)
def eq (o : Ops B W) (a : ByteAuth.Ops B) (x y : W) : B := ByteAuth.equalMask a (bytes o x) (bytes o y)
def bor (a : ByteAuth.Ops B) (x y : B) : B := a.xor (a.xor x y) (a.and x y)

theorem bytes_map {o : Ops B W} {o' : Ops B' W'} {f : B → B'} {fw : W → W'}
    (h : Hom o o' f fw) (x : W) : (bytes o x).map f = bytes o' (fw x) := by
  simp only [bytes, List.map_map, Function.comp_def, h.unpack]

theorem eq_map {o : Ops B W} {o' : Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
    {f : B → B'} {fw : W → W'} (ho : Hom o o' f fw) (ha : ByteAuth.Hom a a' f) (x y : W) :
    f (eq o a x y) = eq o' a' (fw x) (fw y) := by
  simp only [eq, ByteAuth.equalMask_map ha, bytes_map ho]

theorem bor_map {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'}
    (h : ByteAuth.Hom a a' f) (x y : B) : f (bor a x y) = bor a' (f x) (f y) := by
  simp [bor, h.xor, h.and]

theorem bytes_length (o : Ops B W) (x : W) : (bytes o x).length = 8 := by simp [bytes]

theorem ule_value (x y : BitVec 64) : concrete.ule x y = if x.toNat ≤ y.toNat then 255 else 0 := by
  have hx := x.isLt
  have hy := y.isLt
  have he : (((0#1 ++ y) - (0#1 ++ x)).extractLsb' 64 1) =
      (if x.toNat ≤ y.toNat then (0 : BitVec 1) else 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_sub, BitVec.toNat_append,
      BitVec.toNat_ofNat, Nat.zero_mul, Nat.zero_add, Nat.shiftRight_eq_div_pow]
    split <;> simp <;> omega
  simp only [concrete, he]
  split <;> rfl

theorem select_accept (x y : BitVec 64) : concrete.select 255 x y = x := by
  change (BitVec.allOnes 64 &&& x) ^^^ ((0 : BitVec 64) &&& y) = x
  rw [BitVec.allOnes_and]
  simp

theorem select_reject (x y : BitVec 64) : concrete.select 0 x y = y := by
  change ((0 : BitVec 64) &&& x) ^^^ (BitVec.allOnes 64 &&& y) = y
  rw [BitVec.allOnes_and]
  simp

end TlsMpc.Signal.Word64
