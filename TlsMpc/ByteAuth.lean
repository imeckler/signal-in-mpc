import TlsMpc.ByteCircuit

/-!
Secret byte-string comparison and conditional release. Equality is represented
by a secret all-ones byte (255) or zero byte. All loops inspect public lengths;
no branch or array index depends on a secret byte. The output remains shared.
-/

namespace TlsMpc.ByteAuth
open Std.Tactic.BVDecide

structure Ops (B : Type) where
  const : Nat → B
  xor : B → B → B
  and : B → B → B
  not : B → B
  maskBit : B → Nat → B

def concrete : Ops (BitVec 8) where
  const := BitVec.ofNat 8
  xor := (· ^^^ ·)
  and := (· &&& ·)
  not := (~~~·)
  maskBit x i := BitVec.replicate 8 (x.extractLsb' i 1)

def symbolic : Ops (BVExpr 8) where
  const n := .const (BitVec.ofNat 8 n)
  xor x y := BvConstruct.bin x .xor y
  and x y := BvConstruct.bin x .and y
  not x := BvConstruct.un .not x
  maskBit x i := .replicate 8 (BvConstruct.extract i 1 x) rfl

def zeroMask (o : Ops B) (x : B) : B :=
  (List.range 8).foldl (fun mask i => o.and mask (o.not (o.maskBit x i))) (o.const 255)

def eqMask (o : Ops B) (x y : B) : B := zeroMask o (o.xor x y)

def equalMask (o : Ops B) : List B → List B → B
  | [], [] => o.const 255
  | x :: xs, y :: ys => o.and (eqMask o x y) (equalMask o xs ys)
  | _, _ => o.const 0

def release (o : Ops B) (mask : B) (bytes : List B) : List B := bytes.map (o.and mask)

structure Hom (a : Ops B) (b : Ops B') (f : B → B') : Prop where
  const : ∀ n, f (a.const n) = b.const n
  xor : ∀ x y, f (a.xor x y) = b.xor (f x) (f y)
  and : ∀ x y, f (a.and x y) = b.and (f x) (f y)
  not : ∀ x, f (a.not x) = b.not (f x)
  maskBit : ∀ x i, f (a.maskBit x i) = b.maskBit (f x) i

def evaluationHom (assign : BVExpr.Assignment) : Hom symbolic concrete (BVExpr.eval assign) := by
  constructor
  · intro n; rfl
  · intro x y; exact BvConstruct.eval_bin assign x .xor y
  · intro x y; exact BvConstruct.eval_bin assign x .and y
  · intro x; exact BvConstruct.eval_un assign .not x
  · intro x i
    change BVExpr.eval assign (.replicate 8 (BvConstruct.extract i 1 x) rfl) =
      BitVec.replicate 8 ((BVExpr.eval assign x).extractLsb' i 1)
    rw [BVExpr.eval_replicate, BvConstruct.eval_extract]

section Refinement
variable {a : Ops B} {b : Ops B'} {f : B → B'} (h : Hom a b f)
include h

theorem zeroMask_map (x : B) : f (zeroMask a x) = zeroMask b (f x) := by
  have aux (is : List Nat) (mask : B) :
      f (is.foldl (fun m i => a.and m (a.not (a.maskBit x i))) mask) =
        is.foldl (fun m i => b.and m (b.not (b.maskBit (f x) i))) (f mask) := by
    induction is generalizing mask with
    | nil => rfl
    | cons i is ih => simp only [List.foldl_cons, ih, h.and, h.not, h.maskBit]
  simpa [zeroMask, h.const] using aux (List.range 8) (a.const 255)

theorem eqMask_map (x y : B) : f (eqMask a x y) = eqMask b (f x) (f y) := by
  simp [eqMask, zeroMask_map h, h.xor]

theorem equalMask_map (xs ys : List B) :
    f (equalMask a xs ys) = equalMask b (xs.map f) (ys.map f) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [equalMask, h.const]
  | cons x xs ih => cases ys <;> simp [equalMask, h.const, h.and, eqMask_map h, ih]

theorem release_map (mask : B) (bytes : List B) :
    (release a mask bytes).map f = release b (f mask) (bytes.map f) := by
  simp [release, List.map_map, Function.comp_def, h.and]

end Refinement

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zeroMask_value (x : BitVec 8) : zeroMask concrete x = if x = 0 then 255 else 0 := by
  have all : ∀ x : BitVec 8, zeroMask concrete x = if x = 0 then 255 else 0 := by decide +kernel
  exact all x

theorem eqMask_value (x y : BitVec 8) : eqMask concrete x y = if x = y then 255 else 0 := by
  change zeroMask concrete (x ^^^ y) = _
  rw [zeroMask_value]
  have hx : x ^^^ y = 0 ↔ x = y := BitVec.xor_eq_zero_iff
  simp only [hx]

theorem equalMask_value (xs ys : List (BitVec 8)) :
    equalMask concrete xs ys = if xs = ys then 255 else 0 := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [equalMask, concrete]
  | cons x xs ih =>
      cases ys with
      | nil => simp [equalMask, concrete]
      | cons y ys =>
          change (eqMask concrete x y &&& equalMask concrete xs ys) = _
          rw [eqMask_value, ih]
          by_cases hxy : x = y <;> by_cases hrest : xs = ys <;> simp [hxy, hrest]

theorem release_accept (bytes : List (BitVec 8)) : release concrete 255 bytes = bytes := by
  have h : (fun x : BitVec 8 => (255 : BitVec 8) &&& x) = id :=
    funext (fun _ => BitVec.allOnes_and)
  change bytes.map (fun x => (255 : BitVec 8) &&& x) = bytes
  rw [h, List.map_id]

theorem release_reject (bytes : List (BitVec 8)) :
    release concrete 0 bytes = List.replicate bytes.length 0 := by
  induction bytes with
  | nil => rfl
  | cons x xs ih =>
      change (0 &&& x) :: release concrete 0 xs = 0 :: List.replicate xs.length 0
      have hx : (0 : BitVec 8) &&& x = 0 := BitVec.zero_and
      rw [hx, ih]

end TlsMpc.ByteAuth
