import TlsMpc.X25519
import TlsMpc.FieldDagMulti

/-!
A leaner X25519 ladder program for execution on secret shares, proved against
the same RFC 7748 specification as `TlsMpc.X25519`.

Differences from `X25519.compute`, all aimed at the number of multiplications
between secret values:

* each conditional swap of a coordinate pair uses one product, `bit * (b - a)`,
  shared by both outputs (two products per ladder step instead of four);
* the swap bit of every step is an input. For clamped scalar bits `c` the swap at
  step `t` is `c (t+1) xor c t`, an XOR of adjacent scalar bits that the caller
  forms where XOR is free, so no product is spent on it here;
* the program returns the projective pair `(x2, z2)`. The quotient `x2 / z2` is
  left to the caller (see `spec_eq_quotient`), which can invert a masked opening
  instead of running a 254-squaring exponentiation on shares.

Inputs: index `t` for `2 ≤ t ≤ 253` is the swap bit of step `t`; index 256 is
the u-coordinate. Steps 254, 1 and 0 have constant swap bits because of clamping.
-/
namespace TlsMpc.X25519Fast
open FieldDag X25519

/-- Swap a pair when `bit = 1`, using one product. -/
def swapPair (o : X25519.Ops B) (bit a b : B) : B × B :=
  let m := o.mul bit (o.sub b a)
  (o.add a m, o.sub b m)

def swap2 (o : X25519.Ops B) (bit : B) (s : Coordinates B) : Coordinates B :=
  let x := swapPair o bit s.x2 s.x3
  let z := swapPair o bit s.z2 s.z3
  ⟨x.1, z.1, x.2, z.2⟩

/-- Steps `n-1, …, 0`, each a swap by `w t` followed by a ladder step. -/
def ladderDown (o : X25519.Ops B) (u : B) (w : Nat → B) : Nat → Coordinates B → Coordinates B
  | 0, s => s
  | n + 1, s => ladderDown o u w n (advance o u (swap2 o (w n) s))

/-- The swap bit of step `t`: constant where clamping fixes it, an input otherwise. -/
def swapInput (o : X25519.Ops B) (input : Nat → B) (t : Nat) : B :=
  if t = 254 then o.const 1 else if t < 2 then o.const 0 else input t

def compute (o : X25519.Ops B) (input : Nat → B) (u : B) : Coordinates B :=
  ladderDown o u (swapInput o input) 255 ⟨o.const 1, o.const 0, u, o.const 1⟩

/-- The exported program: `x2` then `z2`. -/
def exprs : List Expr :=
  let s := compute X25519.symbolic Expr.input (.input 256)
  [s.x2, s.z2]

/-! ### Specification of the swap bits -/

/-- The clamped scalar bit processed before step `n` (none before step 254). -/
def previous (bits : Nat → Bool) (n : Nat) : Bool := if n = 255 then false else scalarSpec bits n

/-- Swap bit of step `t` for scalar `bits`: for `3 ≤ t ≤ 252` it is
`bits (t+1) xor bits t`; for `t = 253` it is `not (bits 253)`; for `t = 2` it is `bits 3`. -/
def swapBitSpec (bits : Nat → Bool) (t : Nat) : Bool := previous bits (t + 1) ^^ scalarSpec bits t

theorem swapBitSpec_interior (bits : Nat → Bool) (t : Nat) (h3 : 3 ≤ t) (h : t ≤ 252) :
    swapBitSpec bits t = (bits (t + 1) ^^ bits t) := by
  simp only [swapBitSpec, previous, scalarSpec]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem swapBitSpec_top (bits : Nat → Bool) : swapBitSpec bits 253 = !(bits 253) := by
  simp [swapBitSpec, previous, scalarSpec]

theorem swapBitSpec_bottom (bits : Nat → Bool) : swapBitSpec bits 2 = bits 3 := by
  simp [swapBitSpec, previous, scalarSpec]

/-! ### Field identities for the one-product swap -/

private theorem val_sub (x y : F) :
    (x - y).val = if y.val ≤ x.val then x.val - y.val else x.val + modulus - y.val := by
  have hx := x.isLt
  have hy := y.isLt
  rw [Fin.sub_def]
  simp only
  split
  · rw [show modulus - y.val + x.val = x.val - y.val + modulus by omega, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  · rw [show modulus - y.val + x.val = x.val + modulus - y.val by omega]
    exact Nat.mod_eq_of_lt (by omega)

private theorem val_add (x y : F) :
    (x + y).val = if x.val + y.val < modulus then x.val + y.val else x.val + y.val - modulus := by
  have hx := x.isLt
  have hy := y.isLt
  rw [Fin.val_add]
  split
  · exact Nat.mod_eq_of_lt (by assumption)
  · rw [Nat.mod_eq_sub_mod (by omega)]
    exact Nat.mod_eq_of_lt (by omega)

private theorem add_sub_cancel (a b : F) : a + (b - a) = b := by
  apply Fin.eq_of_val_eq
  have ha := a.isLt
  have hb := b.isLt
  rw [val_add, val_sub]
  split <;> split <;> omega

private theorem sub_sub_cancel (a b : F) : b - (b - a) = a := by
  apply Fin.eq_of_val_eq
  have ha := a.isLt
  have hb := b.isLt
  rw [val_sub, val_sub]
  split <;> split <;> omega

private theorem sub_zero (b : F) : b - 0 = b := by
  apply Fin.eq_of_val_eq
  have hb := b.isLt
  rw [val_sub]
  simp

theorem swapPair_value (bit : Bool) (a b : F) :
    swapPair X25519.concrete (bitValue bit) a b = if bit then (b, a) else (a, b) := by
  cases bit
  · change (a + (0 : F) * (b - a), b - (0 : F) * (b - a)) = (a, b)
    rw [Fin.zero_mul, Fin.add_zero, sub_zero]
  · change (a + (1 : F) * (b - a), b - (1 : F) * (b - a)) = (b, a)
    rw [Fin.one_mul, add_sub_cancel, sub_sub_cancel]

theorem swap2_correct (bit : Bool) (s : Coordinates F) :
    swap2 X25519.concrete (bitValue bit) s = swapSpec bit s := by
  cases bit <;> simp [swap2, swapPair_value, swapSpec]

/-! ### The ladder computes the specification's ladder -/

theorem ladderDown_spec (u : F) (bits : Nat → Bool) (w : Nat → F)
    (hw : ∀ t, t < 255 → w t = bitValue (swapBitSpec bits t)) (n : Nat) (hn : n ≤ 255)
    (s : Coordinates F) :
    swapSpec (previous bits 0) (ladderDown X25519.concrete u w n s) =
      ladderSpec u (previous bits n) s ((List.range n).reverse.map (scalarSpec bits)) := by
  induction n generalizing s with
  | zero => simp [ladderDown, ladderSpec]
  | succ n ih =>
    have hlt : n < 255 := by omega
    have hp : previous bits n = scalarSpec bits n := by
      simp only [previous]
      rw [if_neg (by omega)]
    rw [List.range_succ, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
      List.map_cons, ladderDown, ladderSpec]
    rw [hw n hlt, swap2_correct, ih (by omega), hp, swapBitSpec]

/-- With every swap input equal to its specified bit, the program's state is the
state of the specification's ladder. -/
theorem compute_correct (bits : Nat → Bool) (u : F) (input : Nat → F)
    (hin : ∀ t, 2 ≤ t → t ≤ 253 → input t = bitValue (swapBitSpec bits t)) :
    compute X25519.concrete input u =
      ladderSpec u false ⟨1, 0, u, 1⟩ ((List.range 255).reverse.map (scalarSpec bits)) := by
  have hw : ∀ t, t < 255 → swapInput X25519.concrete input t = bitValue (swapBitSpec bits t) := by
    intro t ht
    unfold swapInput
    split
    · rename_i h
      subst h
      simp [swapBitSpec, previous, scalarSpec]
      rfl
    · split
      · rename_i h2
        have : swapBitSpec bits t = false := by
          simp only [swapBitSpec, previous, scalarSpec]
          rw [if_neg (by omega), if_pos (by omega), if_pos (by omega)]
          rfl
        rw [this]
        rfl
      · exact hin t (by omega) (by omega)
  have h := ladderDown_spec u bits (swapInput X25519.concrete input) hw 255 (by omega)
    ⟨concrete.const 1, X25519.concrete.const 0, u, X25519.concrete.const 1⟩
  have h0 : previous bits 0 = false := by simp [previous, scalarSpec]
  have h255 : previous bits 255 = false := by simp [previous]
  rw [h0, h255] at h
  simp only [swapSpec, Bool.false_eq_true, if_false] at h
  unfold compute
  rw [h]
  rfl

/-- The RFC result is the quotient of the program's two outputs. -/
theorem spec_eq_quotient (bits : Nat → Bool) (u : F) (input : Nat → F)
    (hin : ∀ t, 2 ≤ t → t ≤ 253 → input t = bitValue (swapBitSpec bits t)) :
    spec bits u = (compute X25519.concrete input u).x2 * inverse X25519.concrete (compute X25519.concrete input u).z2 := by
  rw [compute_correct bits u input hin]
  rfl

/-! ### Symbolic refinement -/

section Refinement
variable {a : X25519.Ops B} {b : X25519.Ops C} {f : B → C} (h : Hom a b f)
include h

theorem swap2_map (bit : B) (s : Coordinates B) :
    (swap2 a bit s).map f = swap2 b (f bit) (s.map f) := by
  simp only [swap2, swapPair, Coordinates.map, h.add, h.sub, h.mul]

theorem ladderDown_map (u : B) (w : Nat → B) (n : Nat) (s : Coordinates B) :
    (ladderDown a u w n s).map f = ladderDown b (f u) (f ∘ w) n (s.map f) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [ladderDown, ih, advance_map h, swap2_map h, Function.comp]

theorem swapInput_map (input : Nat → B) (t : Nat) :
    f (swapInput a input t) = swapInput b (f ∘ input) t := by
  unfold swapInput
  split
  · exact h.const 1
  · split
    · exact h.const 0
    · rfl

theorem compute_map (input : Nat → B) (u : B) :
    (compute a input u).map f = compute b (f ∘ input) (f u) := by
  have hw : (f ∘ swapInput a input) = swapInput b (f ∘ input) := by
    funext t
    exact swapInput_map h input t
  unfold compute
  rw [ladderDown_map h, hw]
  simp only [Coordinates.map, h.const]
end Refinement

/-- Assignment for the exported program: swap bits at 2..253, `u` at 256. -/
def assignment (bits : Nat → Bool) (u : F) (i : Nat) : F :=
  if i = 256 then u else bitValue (swapBitSpec bits i)

/-- Every accepted compilation of the exported program outputs a pair whose
quotient is the RFC 7748 result. -/
theorem compiled_correct (bits : Nat → Bool) (u : F) (artifact : FieldDag.MultiArtifact)
    (compiled : FieldDag.compileAll exprs = some artifact) :
    ∃ x z, artifact.outputs.map
        (FieldDag.result (FieldDag.concrete (assignment bits u)) artifact.nodes) = [x, z] ∧
      spec bits u = x * inverse X25519.concrete z := by
  have hc := FieldDag.compileAll_correct _ _ compiled (assignment bits u)
  have hm := compute_map (evaluationHom (assignment bits u)) Expr.input (.input 256)
  have hin : ∀ t, 2 ≤ t → t ≤ 253 →
      (Expr.eval (assignment bits u) ∘ Expr.input) t = bitValue (swapBitSpec bits t) := by
    intro t _ ht
    simp only [Function.comp, Expr.eval, assignment]
    rw [if_neg (by omega)]
  have hu : Expr.eval (assignment bits u) (.input 256) = u := by simp [Expr.eval, assignment]
  rw [hu] at hm
  refine ⟨_, _, ?_, spec_eq_quotient bits u _ hin⟩
  rw [hc, ← hm]
  rfl

#print axioms compute_correct
#print axioms spec_eq_quotient
#print axioms compiled_correct

end TlsMpc.X25519Fast
