import TlsMpc.ByteCircuit

/-!
GHASH, NIST SP 800-38D sections 6.3 and 6.4. Blocks use network byte order:
the most significant bit is the coefficient of x^0 in the standard's field
encoding. This is binary-polynomial arithmetic, not prime-field arithmetic.
The 128 shifted multiples of H are prepared once and shared across blocks.
No secret value controls indexing, loops, I/O or output release.
-/

namespace TlsMpc.Ghash
open Std.Tactic.BVDecide

structure Ops (W : Type) where
  const : Nat → W
  xor : W → W → W
  and : W → W → W
  shr : W → W
  maskBit : W → Nat → W

def concrete : Ops (BitVec 128) where
  const := BitVec.ofNat 128
  xor := (· ^^^ ·)
  and := (· &&& ·)
  shr x := x.extractLsb' 1 128
  maskBit x i := BitVec.replicate 128 (x.extractLsb' i 1)

def symbolic : Ops (BVExpr 128) where
  const n := .const (BitVec.ofNat 128 n)
  xor a b := BvConstruct.bin a .xor b
  and a b := BvConstruct.bin a .and b
  shr x := BvConstruct.extract 1 128 x
  maskBit x i := .replicate 128 (BvConstruct.extract i 1 x) rfl

def reduction : Nat := 0xe1000000000000000000000000000000

def nextPower (o : Ops W) (v : W) : W :=
  o.xor (o.shr v) (o.and (o.maskBit v 0) (o.const reduction))

def powers (o : Ops W) : Nat → W → List W
  | 0, _ => []
  | n + 1, v => v :: powers o n (nextPower o v)

def multiplyLoop (o : Ops W) (x : W) : List W → Nat → W → W
  | [], _, z => z
  | v :: rest, i, z => multiplyLoop o x rest (i + 1)
      (o.xor z (o.and (o.maskBit x (127 - i)) v))

def multiplyPrepared (o : Ops W) (table : List W) (x : W) : W :=
  multiplyLoop o x table 0 (o.const 0)

def multiply (o : Ops W) (x h : W) : W :=
  multiplyPrepared o (powers o 128 h) x

def fold (o : Ops W) (h : W) : List W → W → W
  | [], y => y
  | block :: rest, y => fold o h rest (multiply o (o.xor y block) h)

def hash (o : Ops W) (h : W) (blocks : List W) : W := fold o h blocks (o.const 0)

def foldPrepared (o : Ops W) (table : List W) : List W → W → W
  | [], y => y
  | block :: rest, y => foldPrepared o table rest (multiplyPrepared o table (o.xor y block))

def hashFast (o : Ops W) (h : W) (blocks : List W) : W :=
  foldPrepared o (powers o 128 h) blocks (o.const 0)

theorem foldPrepared_correct (o : Ops W) (h : W) (blocks : List W) (y : W) :
    foldPrepared o (powers o 128 h) blocks y = fold o h blocks y := by
  induction blocks generalizing y with
  | nil => rfl
  | cons block rest ih => simp only [foldPrepared, fold, multiply, ih]

theorem hashFast_correct (o : Ops W) (h : W) (blocks : List W) :
    hashFast o h blocks = hash o h blocks := foldPrepared_correct o h blocks _

structure Hom (a : Ops W) (b : Ops W') (f : W → W') : Prop where
  const : ∀ n, f (a.const n) = b.const n
  xor : ∀ x y, f (a.xor x y) = b.xor (f x) (f y)
  and : ∀ x y, f (a.and x y) = b.and (f x) (f y)
  shr : ∀ x, f (a.shr x) = b.shr (f x)
  maskBit : ∀ x i, f (a.maskBit x i) = b.maskBit (f x) i

def evaluationHom (assign : BVExpr.Assignment) : Hom symbolic concrete (BVExpr.eval assign) := by
  constructor
  · intro n; rfl
  · intro x y; exact BvConstruct.eval_bin assign x .xor y
  · intro x y; exact BvConstruct.eval_bin assign x .and y
  · intro x; exact BvConstruct.eval_extract assign 1 128 x
  · intro x i
    change BVExpr.eval assign (.replicate 128 (BvConstruct.extract i 1 x) rfl) =
      BitVec.replicate 128 ((BVExpr.eval assign x).extractLsb' i 1)
    rw [BVExpr.eval_replicate, BvConstruct.eval_extract]

section Refinement
variable {a : Ops W} {b : Ops W'} {f : W → W'} (h : Hom a b f)
include h

theorem nextPower_map (v : W) : f (nextPower a v) = nextPower b (f v) := by
  simp [nextPower, h.xor, h.and, h.maskBit, h.shr, h.const]

theorem powers_map (n : Nat) (v : W) : (powers a n v).map f = powers b n (f v) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [powers, ih, nextPower_map h]

theorem multiplyLoop_map (x : W) (table : List W) (i : Nat) (z : W) :
    f (multiplyLoop a x table i z) = multiplyLoop b (f x) (table.map f) i (f z) := by
  induction table generalizing i z with
  | nil => rfl
  | cons v rest ih => simp [multiplyLoop, ih, h.xor, h.and, h.maskBit]

theorem multiply_map (x key : W) : f (multiply a x key) = multiply b (f x) (f key) := by
  simp [multiply, multiplyPrepared, multiplyLoop_map h, powers_map h, h.const]

theorem multiplyPrepared_map (table : List W) (x : W) :
    f (multiplyPrepared a table x) = multiplyPrepared b (table.map f) (f x) := by
  simp [multiplyPrepared, multiplyLoop_map h, h.const]

theorem foldPrepared_map (table blocks : List W) (y : W) :
    f (foldPrepared a table blocks y) = foldPrepared b (table.map f) (blocks.map f) (f y) := by
  induction blocks generalizing y with
  | nil => rfl
  | cons block rest ih => simp [foldPrepared, ih, multiplyPrepared_map h, h.xor]

theorem fold_map (key : W) (blocks : List W) (y : W) :
    f (fold a key blocks y) = fold b (f key) (blocks.map f) (f y) := by
  induction blocks generalizing y with
  | nil => rfl
  | cons block rest ih => simp [fold, ih, multiply_map h, h.xor]

theorem hash_map (key : W) (blocks : List W) :
    f (hash a key blocks) = hash b (f key) (blocks.map f) := by
  simp [hash, fold_map h, h.const]

end Refinement

/-- Inputs here are normally exactly sixteen bytes. A shorter input is
left-padded, and a longer input truncated, by this internal total function. -/
def packValue (bytes : List (BitVec 8)) : BitVec 128 := (ByteCircuit.joinValue bytes).setWidth 128
def packExpr (bytes : List (BVExpr 8)) : BVExpr 128 :=
  BvConstruct.extract 0 128 (ByteCircuit.joinExpr bytes)

def unpackValue (word : BitVec 128) : List (BitVec 8) :=
  (List.range 16).map (fun i => word.extractLsb' (8 * (15 - i)) 8)
def unpackExpr (word : BVExpr 128) : List (BVExpr 8) :=
  (List.range 16).map (fun i => BvConstruct.extract (8 * (15 - i)) 8 word)

theorem pack_refines (assign : BVExpr.Assignment) (bytes : List (BVExpr 8)) :
    BVExpr.eval assign (packExpr bytes) = packValue (bytes.map (BVExpr.eval assign)) := by
  apply BitVec.eq_of_toNat_eq
  simp [packExpr, packValue, ByteCircuit.joinExpr_correct]

theorem unpack_refines (assign : BVExpr.Assignment) (word : BVExpr 128) :
    (unpackExpr word).map (BVExpr.eval assign) = unpackValue (BVExpr.eval assign word) := by
  simp [unpackExpr, unpackValue, List.map_map, Function.comp_def]

theorem compiled_hashFast_correct (key : BVExpr 128) (blocks : List (BVExpr 128))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (unpackExpr (hashFast symbolic key blocks)).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile
        (ByteCircuit.joinExpr (unpackExpr (hashFast symbolic key blocks)))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile
        (ByteCircuit.joinExpr (unpackExpr (hashFast symbolic key blocks)))).vec.get index hi)) =
    (ByteCircuit.joinValue (unpackValue (hash concrete (BVExpr.eval assign key)
      (blocks.map (BVExpr.eval assign))))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, unpack_refines, hashFast_correct, hash_map (evaluationHom assign)]

end TlsMpc.Ghash
