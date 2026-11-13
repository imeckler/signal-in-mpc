import TlsMpc.Node.Flows.CurveProofs

/-!
# The facts liveness rests on, and the local functions that cannot fail under them (F33, F28)

Stage S11. The local arithmetic (`Local/Field`, `Local/Edwards`) and the lift's public root return
`none` (and the flows then abort) on a failed square root. This file states, as named hypotheses,
the field facts that rule that out on honest inputs, and proves from them that the functions never
return `none` there:

  * `FieldInverse` (`FieldDagV3`): every nonzero `x` has `x · x^(p−2) = 1` (Fermat). Discharged in
    `proofs/` by `toZMod_inverse` (the main package's inverse is the `ZMod p` inverse).
  * `EulerCriterion` (`CurveProofs`): a nonzero `x` is a square iff `x^((p−1)/2) = 1`. Discharged in
    `proofs/` by `euler_criterion` (with `Local.Field.pow_eq`).
  * `TwoNonSquare` (`CurveProofs`, H-QR): 2 is not a square. Discharged in `proofs/` by
    `two_not_square`.
  * `CompleteAddition` (here): on two curve points the addition's `y` denominator
    `1 − d·x₁x₂y₁y₂` is not zero. Discharged in `proofs/` by `edwards_complete` (Bernstein–Lange,
    `Point.denom_y_ne_zero`), transported by `toZMod`.

PROVED from them (standard axioms only):
  * `fermat`, `euler_cases`: `x^(p−1) = 1` and `x^((p−1)/2) = ±1` for `x ≠ 0` (`FieldInverse`);
  * `sqrt_complete`: `Local.Field.sqrt` returns a root of every square (`FieldInverse`,
    `EulerCriterion`): the candidate `x^((p+3)/8)` squares to `±x`;
  * `root_isSome`, `roots_isSome`: the lift's public root never fails on a nonzero `w`, so the
    lift's "lift root" abort never fires (with `TwoNonSquare`: `w` or `w/2` is a square);
  * `addU_den_ne_zero` (F28): the split agreement's `den ≠ 0` on curve points under
    `CompleteAddition`, and `splitAgree_montU`: the handle the two honest parties end with holds
    `montU (T_A + T_B)` with no `den` hypothesis left (`splitAgree_honest`, `addU_montU`).

NOT covered here (gaps, tested only): `decode (encode P) = some P` for curve points, and the batched
inversion `toAffineAll` succeeding on nonzero `Z` (used by `hints`, `publicTable`).
-/

namespace TlsMpc.Node.Flows.Curve

open TlsMpc.FieldDag (F modulus ofNat power inverse)
open TlsMpc.FieldDag.V3 (FieldInverse power_add mul_ne_zero)
open TlsMpc.Node.Local.Field (sqrt pow pow_eq euler sqrtM1 inv inv_eq)

theorem one_eq : (ofNat 1 : F) = 1 := rfl

theorem power_double (x : F) (k : Nat) : power x k * power x k = power x (2 * k) := by
  rw [show 2 * k = k + k by omega, power_add]

theorem power_succ' (x : F) (k : Nat) : power x (k + 1) = x * power x k := rfl

theorem power_one_base (k : Nat) : power (ofNat 1) k = ofNat 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [power_succ', ih, one_eq]; grind

theorem power_zero_base (k : Nat) : power 0 (k + 1) = 0 := by
  rw [power_succ']; grind

/-- **Fermat** (`FieldInverse`): `x^(p−1) = 1` for `x ≠ 0`. -/
theorem fermat (hinv : FieldInverse) (x : F) (hx : x ≠ 0) : power x (modulus - 1) = 1 := by
  have h := hinv x hx
  unfold inverse at h
  rw [show modulus - 1 = (modulus - 2) + 1 by decide, power_succ']
  exact h

theorem neg_mul_left (a b : F) : (0 - a) * b = 0 - a * b := by grind

theorem one_mul_F (b : F) : 1 * b = b := by grind

theorem cancel_unit (a e : F) (ha : a * a = 1) (h : a * e = 1) : e = a := by grind

theorem add_one_zero (y : F) (e : y + 1 = 0) : y = 0 - 1 :=
  calc y = (y + 1) - 1 := by grind
    _ = 0 - 1 := by rw [e]

/-- `y² = 1` has only the roots `±1` (no zero divisors, `FieldInverse`). -/
theorem sq_one (hinv : FieldInverse) (y : F) (h : y * y = 1) : y = 1 ∨ y = 0 - 1 := by
  rcases Classical.em (y = 1) with h1 | h1
  · exact Or.inl h1
  · right
    apply Classical.byContradiction
    intro h2
    have a : y - 1 ≠ 0 := fun e => h1 (by grind)
    have b : y + 1 ≠ 0 := fun e => h2 (add_one_zero y e)
    exact mul_ne_zero hinv a b (by grind)

/-- **Euler's power is ±1** on nonzero elements (`FieldInverse`). -/
theorem euler_cases (hinv : FieldInverse) (x : F) (hx : x ≠ 0) : euler x = ofNat 1 ∨ euler x = 0 - ofNat 1 := by
  have h : euler x * euler x = 1 := by
    rw [euler, pow_eq, power_double, show 2 * ((modulus - 1) / 2) = modulus - 1 by decide]
    exact fermat hinv x hx
  exact sq_one hinv _ h

/-- **`sqrt` finds a root of every square** (`FieldInverse`, `EulerCriterion`). -/
theorem sqrt_complete (hinv : FieldInverse) (hE : EulerCriterion) (x : F) (hsq : ∃ r, r * r = x) :
    (sqrt x).isSome = true := by
  unfold sqrt
  dsimp only
  rcases Classical.em (x = 0) with hx | hx
  · subst hx
    have hc : pow 0 ((modulus + 3) / 8) = 0 := by
      rw [pow_eq, show (modulus + 3) / 8 = ((modulus + 3) / 8 - 1) + 1 by decide, power_zero_base]
    rw [if_pos (by rw [hc]; grind)]
    rfl
  · have he : euler x = ofNat 1 := (hE x hx).mp hsq
    have hy : power x ((modulus - 1) / 4) * power x ((modulus - 1) / 4) = 1 := by
      rw [power_double, show 2 * ((modulus - 1) / 4) = (modulus - 1) / 2 by decide, ← pow_eq]
      exact he
    have hc : pow x ((modulus + 3) / 8) * pow x ((modulus + 3) / 8) = power x ((modulus - 1) / 4) * x := by
      rw [pow_eq, power_double, show 2 * ((modulus + 3) / 8) = (modulus - 1) / 4 + 1 by decide, power_add]
      show power x ((modulus - 1) / 4) * (x * ofNat 1) = _
      rw [one_eq]
      grind
    rcases sq_one hinv _ hy with h1 | h1
    · rw [if_pos (by rw [hc, h1, one_mul_F])]
      rfl
    · by_cases h2 : pow x ((modulus + 3) / 8) * pow x ((modulus + 3) / 8) = x
      · rw [if_pos h2]; rfl
      · rw [if_neg h2, if_pos (by rw [hc, h1, neg_mul_left, one_mul_F])]
        rfl

theorem euler_mul (x y : F) : euler (x * y) = euler x * euler y := by
  rw [euler, euler, euler, pow_eq, pow_eq, pow_eq, power_mul]

/-- **The lift's public root never fails on a nonzero `w`** (`FieldInverse`, `EulerCriterion`,
`TwoNonSquare`): `w` is a square or `w/2` is. -/
theorem root_isSome (hinv : FieldInverse) (hE : EulerCriterion) (hQR : TwoNonSquare) (w : F) (hw : w ≠ 0) :
    (TlsMpc.Node.Local.Edwards.root w).isSome = true := by
  have h2 : (ofNat 2 : F) ≠ 0 := by decide
  have hi2 : inverse (ofNat 2) ≠ 0 := by
    intro e; have := hinv _ h2; rw [e] at this; grind
  have he2 : euler (ofNat 2) = 0 - ofNat 1 := by
    rcases euler_cases hinv _ h2 with h | h
    · exact absurd ((hE _ h2).mpr h) hQR
    · exact h
  have hei : euler (inverse (ofNat 2)) = 0 - ofNat 1 := by
    have hm : euler (ofNat 2 * inverse (ofNat 2)) = ofNat 1 := by
      rw [hinv _ h2, ← one_eq, euler, pow_eq, power_one_base]
    rw [euler_mul, he2] at hm
    have : (0 - ofNat 1 : F) * (0 - ofNat 1) = ofNat 1 := by decide
    rw [one_eq] at hm this
    exact cancel_unit _ _ this hm
  unfold TlsMpc.Node.Local.Edwards.root
  dsimp only
  have hsq : ∃ r, r * r = (if (euler w == ofNat 1) = true then w else w * inv (ofNat 2)) := by
    split
    · next h => exact (hE w hw).mpr (by simpa using h)
    · next h =>
      have hne : euler w = 0 - ofNat 1 := by
        rcases euler_cases hinv w hw with h' | h'
        · exact absurd (by simp [h']) h
        · exact h'
      rw [inv_eq]
      refine (hE _ (mul_ne_zero hinv hw hi2)).mpr ?_
      rw [euler_mul, hne, hei]
      decide
  have := sqrt_complete hinv hE _ hsq
  revert this
  cases sqrt (if (euler w == ofNat 1) = true then w else w * inv (ofNat 2)) with
  | none => simp
  | some s => intro _; rfl

/-- **The lift's roots never fail** (so its "lift root" abort never fires). -/
theorem roots_isSome (hinv : FieldInverse) (hE : EulerCriterion) (hQR : TwoNonSquare) :
    ∀ ws : List F, (roots ws).isSome = true
  | [] => rfl
  | w :: ws => by
    have ih := roots_isSome hinv hE hQR ws
    unfold roots at ih ⊢
    rw [List.mapM_cons]
    obtain ⟨rs, hrs⟩ := Option.isSome_iff_exists.mp ih
    rw [hrs]
    split
    · rfl
    · next hw =>
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (root_isSome hinv hE hQR w hw)
      rw [hr]
      rfl

/-! ## F28: the split agreement's denominator on curve points -/

/-- **Complete addition** (named hypothesis; `proofs/` `edwards_complete`, `Point.denom_y_ne_zero`):
on two curve points the `y` denominator of the Edwards addition is not zero. -/
def CompleteAddition : Prop :=
  ∀ x1 y1 x2 y2 : F, TlsMpc.Node.Local.Edwards.curveValue (x1, y1) = 0 →
    TlsMpc.Node.Local.Edwards.curveValue (x2, y2) = 0 →
    ofNat 1 - TlsMpc.Node.Local.Edwards.dK * (x1 * x2 * (y1 * y2)) ≠ 0

/-- **F28**: `edwards-add-u`'s denominator `121666 + 121665·x₁x₂y₁y₂ = 121666·(1 − d·x₁x₂y₁y₂)` is
nonzero on curve points. -/
theorem addU_den_ne_zero (hinv : FieldInverse) (hC : CompleteAddition) (x1 y1 x2 y2 : F)
    (h1 : TlsMpc.Node.Local.Edwards.curveValue (x1, y1) = 0) (h2 : TlsMpc.Node.Local.Edwards.curveValue (x2, y2) = 0) :
    ofNat 121666 + ofNat 121665 * (x1 * x2 * (y1 * y2)) ≠ 0 := by
  have hc := hC x1 y1 x2 y2 h1 h2
  have hk : (ofNat 121666 : F) ≠ 0 := by decide
  have hd := TlsMpc.Node.Local.Edwards.dK_scaled
  have e : ofNat 121666 + ofNat 121665 * (x1 * x2 * (y1 * y2)) =
      ofNat 121666 * (ofNat 1 - TlsMpc.Node.Local.Edwards.dK * (x1 * x2 * (y1 * y2))) := by
    generalize TlsMpc.Node.Local.Edwards.dK = d at hd ⊢
    rw [one_eq]
    grind
  rw [e]
  exact mul_ne_zero hinv hk hc

/-- **P-SPLIT (a), with F28 closed**: two honest parties' `splitAgree` (the hypotheses of
`splitAgree_honest`) leave the agreement handle holding `montU (T_A + T_B)`, the Montgomery
coordinate of the sum of the two parties' points (`Local.Edwards.add` = `pointAddValue`, the group
law by `proofs/` R7), with the denominator fact from `CompleteAddition` instead of a hypothesis. -/
theorem splitAgree_montU (hinv : FieldInverse) (hC : CompleteAddition) (E : TlsMpc.Node.Engine.Env)
    (pOn pAdd : TlsMpc.FieldDag.V3.Program)
    (hOn : E.programs onCurveName = some pOn) (hAdd : E.programs addUName = some pAdd)
    (hOnC : Conv.Computes pOn 2 [.pub] (fun i => [TlsMpc.EdwardsShare.onCurve.eval i]))
    (hAddC : Conv.Computes pAdd 4 [.never, .never] (fun i => TlsMpc.EdwardsShare.addU.map (TlsMpc.FieldDag.Expr.eval i)))
    (hq : E.programs Inversion.quotientName = some TlsMpc.FieldDag.V3.quotient)
    (σA σB : TlsMpc.Node.Engine.Store) (I : TlsMpc.Node.Engine.Ideal) (f0 tSlot maskSlot : Nat) (xA yA xB yB mA mB : F)
    (hA : σA.elems tSlot = [xA, yA]) (hB : σB.elems tSlot = [xB, yB])
    (hmA : σA.elems maskSlot = [mA]) (hmB : σB.elems maskSlot = [mB]) (hm : mA + mB ≠ 0)
    (hcA : TlsMpc.Node.Local.Edwards.curveValue (xA, yA) = 0) (hcB : TlsMpc.Node.Local.Edwards.curveValue (xB, yB) = 0) :
    (TlsMpc.Node.Engine.jointRun E (splitAgree f0 tSlot maskSlot) (splitAgree f0 tSlot maskSlot) σA σB I).ideal.fields
        (f0 + 11) =
      some (TlsMpc.Node.Local.Edwards.montU (TlsMpc.Node.Local.Edwards.add (xA, yA) (xB, yB))) := by
  have h := (splitAgree_honest hinv E pOn pAdd hOn hAdd hOnC hAddC hq σA σB I f0 tSlot maskSlot xA yA xB yB mA mB
    hA hB hmA hmB hm hcA hcB).2
  rw [h, addU_montU hinv xA yA xB yB (addU_den_ne_zero hinv hC xA yA xB yB hcA hcB)]

end TlsMpc.Node.Flows.Curve
