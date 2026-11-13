import TlsMpc.Node.Flows.CurveProgLive

/-!
# The batched inversion succeeds on nonzero `Z` (PROOF_GAPS F25b)

Stage S11. `Local.Edwards.toAffineAll` (Montgomery's trick, checked: it returns `none` unless every
`z·w = 1`) is used by the local step's `hints` and by `publicTable`. Proved here (standard axioms,
under the named hypotheses below):

  * `backward_inv`: the backward pass computes `z₁⁻¹ … zₙ⁻¹` from `(z₁⋯zₙ)⁻¹` and the prefix
    products, when every `zᵢ ≠ 0` (`FieldInverse`);
  * `invAll_some`: `invAll zs = some (zs.map inverse)` when every `z ≠ 0`, so its check passes;
  * `toAffineAll_isSome`: `toAffineAll` succeeds on extended points with nonzero `Z`;
  * `windowBases_good`, `hints_isSome`: the 63 window bases of a curve point are represented
    points (`ExtClosed`, `proofs/` `extAddValue_is_group_add`), so this party's hints never fail
    when its hinted point (`Z − M_A` for A: `AddClosed`; `M_B` for B) is a curve point;
  * `publicTable_isSome`: the public table of a curve point never fails.
-/

namespace TlsMpc.Node.Flows.Curve

open TlsMpc.Node.Engine (Party)
open TlsMpc.FieldDag (F ofNat inverse)
open TlsMpc.FieldDag.V3 (FieldInverse mul_ne_zero)
open TlsMpc.Node.Local.Edwards (curveValue)

namespace LL

/-- The product of a list. -/
def prodF (l : List F) : F := l.foldl (· * ·) (ofNat 1)

theorem prodF_snoc (l : List F) (z : F) : prodF (l ++ [z]) = prodF l * z := by
  simp [prodF, List.foldl_append]

theorem foldl_mul_ne (hinv : FieldInverse) : ∀ (l : List F) (acc : F), acc ≠ 0 → (∀ z ∈ l, z ≠ 0) →
    l.foldl (· * ·) acc ≠ 0
  | [], _, h, _ => h
  | z :: l, acc, h, hl => foldl_mul_ne hinv l (acc * z) (mul_ne_zero hinv h (hl z (by simp)))
      (fun x hx => hl x (by simp [hx]))

theorem prodF_ne (hinv : FieldInverse) (l : List F) (h : ∀ z ∈ l, z ≠ 0) : prodF l ≠ 0 :=
  foldl_mul_ne hinv l (ofNat 1) (by decide) h

theorem scan_snoc (l : List F) (z : F) :
    (l ++ [z]).scanl (· * ·) (ofNat 1) = l.scanl (· * ·) (ofNat 1) ++ [prodF l * z] := by
  rw [List.scanl_append]
  simp [prodF]

theorem scan_last (l : List F) : (l.scanl (· * ·) (ofNat 1)).getLastD (ofNat 1) = prodF l := by
  rw [List.getLastD_eq_getLast?, List.getLast?_scanl]
  rfl

theorem scan_reverse (l : List F) :
    (l.scanl (· * ·) (ofNat 1)).reverse = prodF l :: (l.scanl (· * ·) (ofNat 1)).dropLast.reverse := by
  have hne : l.scanl (· * ·) (ofNat 1) ≠ [] := by simp
  conv => lhs; rw [← List.dropLast_concat_getLast hne]
  rw [List.reverse_append, List.getLast_scanl]
  simp [prodF]

theorem inv_mul_right (hinv : FieldInverse) (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    inverse (a * b) * b = inverse a := by
  have hab := hinv (a * b) (mul_ne_zero hinv ha hb)
  have h1 := hinv a ha
  generalize inverse (a * b) = c at hab ⊢
  generalize inverse a = ia at h1 ⊢
  calc c * b = c * b * (a * ia) := by rw [h1]; grind
    _ = (a * b * c) * ia := by grind
    _ = ia := by rw [hab]; grind

theorem inv_mul_left (hinv : FieldInverse) (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    inverse (a * b) * a = inverse b := by
  rw [show a * b = b * a by grind]
  exact inv_mul_right hinv b a hb ha

theorem backward_inv_rev (hinv : FieldInverse) : ∀ (r : List F), (∀ z ∈ r, z ≠ 0) → ∀ out : List F,
    TlsMpc.Node.Local.Edwards.backward r.reverse.reverse (r.reverse.scanl (· * ·) (ofNat 1)).dropLast.reverse
      (inverse (prodF r.reverse)) out = r.reverse.map inverse ++ out
  | [], _, out => rfl
  | z :: r, hnz, out => by
    have ih := backward_inv_rev hinv r (fun x hx => hnz x (by simp [hx]))
    rw [List.reverse_cons]
    have hl : ∀ x ∈ r.reverse, x ≠ 0 := fun x hx => hnz x (by simp at hx; simp [hx])
    have hz : z ≠ 0 := hnz z (by simp)
    generalize r.reverse = l at ih hl ⊢
    have hp := prodF_ne hinv l hl
    rw [List.reverse_append, scan_snoc, List.dropLast_concat, scan_reverse, prodF_snoc]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
    show TlsMpc.Node.Local.Edwards.backward l.reverse _ (inverse (prodF l * z) * z)
      ((inverse (prodF l * z) * prodF l) :: out) = _
    rw [inv_mul_right hinv _ _ hp hz, inv_mul_left hinv _ _ hp hz, ih]
    simp

/-- **The backward pass computes the inverses** (every `zᵢ ≠ 0`). -/
theorem backward_inv (hinv : FieldInverse) (l : List F) (h : ∀ z ∈ l, z ≠ 0) (out : List F) :
    TlsMpc.Node.Local.Edwards.backward l.reverse (l.scanl (· * ·) (ofNat 1)).dropLast.reverse (inverse (prodF l)) out =
      l.map inverse ++ out := by
  have := backward_inv_rev hinv l.reverse (fun z hz => h z (List.mem_reverse.mp hz)) out
  simpa only [List.reverse_reverse] using this

theorem zip_map_self (l : List F) : l.zip (l.map inverse) = l.map (fun z => (z, inverse z)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- **`invAll` succeeds on nonzero elements**, with the inverses. -/
theorem invAll_some (hinv : FieldInverse) (zs : List F) (h : ∀ z ∈ zs, z ≠ 0) :
    TlsMpc.Node.Local.Edwards.invAll zs = some (zs.map inverse) := by
  unfold TlsMpc.Node.Local.Edwards.invAll
  dsimp only
  rw [scan_last, TlsMpc.Node.Local.Field.inv_eq, backward_inv hinv zs h [], List.append_nil]
  rw [if_pos]
  refine ⟨by simp, ?_⟩
  rw [List.all_eq_true, zip_map_self]
  intro e he
  simp only [List.mem_map] at he
  obtain ⟨z, hz, rfl⟩ := he
  rw [hinv z (h z hz)]
  decide

/-- **F25b: `toAffineAll` succeeds on extended points with nonzero `Z`.** -/
theorem toAffineAll_isSome (hinv : FieldInverse) (es : List TlsMpc.Node.Local.Edwards.ExtV) (h : ∀ e ∈ es, e.z ≠ 0) :
    (TlsMpc.Node.Local.Edwards.toAffineAll es).isSome := by
  unfold TlsMpc.Node.Local.Edwards.toAffineAll
  rw [invAll_some hinv _ (by
    intro z hz
    simp only [List.mem_map] at hz
    obtain ⟨e, he, rfl⟩ := hz
    exact h e he)]
  rfl

theorem times16_good (hX : ExtClosed) (p : TlsMpc.Node.Local.Edwards.ExtV) (hp : ExtGood p) :
    ExtGood (TlsMpc.Node.Local.Edwards.times16 p) := by
  have h2 := hX p p hp hp
  have h4 := hX _ _ h2 h2
  have h8 := hX _ _ h4 h4
  exact hX _ _ h8 h8

/-- The window bases of a curve point are represented points. -/
theorem windowBases_good (hX : ExtClosed) (q : TlsMpc.Node.Local.Edwards.Value) (hq : curveValue q = 0) :
    ∀ e ∈ TlsMpc.Node.Local.Edwards.windowBases q, ExtGood e := by
  have := PL.foldl_inv (fun (st : List TlsMpc.Node.Local.Edwards.ExtV × TlsMpc.Node.Local.Edwards.ExtV) =>
      (∀ e ∈ st.1, ExtGood e) ∧ ExtGood st.2)
    (fun (st : List TlsMpc.Node.Local.Edwards.ExtV × TlsMpc.Node.Local.Edwards.ExtV) (_ : Nat) =>
      (TlsMpc.Node.Local.Edwards.times16 st.2 :: st.1, TlsMpc.Node.Local.Edwards.times16 st.2))
    (fun st _ h => by
      refine ⟨fun e he => ?_, times16_good hX _ h.2⟩
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact times16_good hX _ h.2
      · exact h.1 e he)
    (List.range 63) ([], TlsMpc.Node.Local.Edwards.ofAffine q) ⟨fun e he => by simp at he, PL.ofAffineValue_good q hq⟩
  intro e he
  exact this.1 e (List.mem_reverse.mp he)

/-- The point a party hints is a curve point when `Z` and its mask point are (`AddClosed`; the
negation keeps the curve equation). -/
theorem hintBase_on (hA : AddClosed) (me : Party) (z mask : TlsMpc.Node.Local.Edwards.Value)
    (hz : curveValue z = 0) (hm : curveValue mask = 0) :
    curveValue (TlsMpc.Node.Local.Edwards.hintBase me z mask) = 0 := by
  cases me with
  | a =>
    show curveValue (TlsMpc.Node.Local.Edwards.add z (ofNat 0 - mask.1, mask.2)) = 0
    rw [TlsMpc.Node.Local.Edwards.add_eq]
    exact hA _ _ hz (by rw [PL.curveValue_neg]; exact hm)
  | b => exact hm

/-- **This party's hints never fail** (F25b for `hints`): `Z` and its mask point on the curve. -/
theorem hints_isSome (hinv : FieldInverse) (hA : AddClosed) (hX : ExtClosed) (me : Party)
    (z mask : TlsMpc.Node.Local.Edwards.Value) (hz : curveValue z = 0) (hm : curveValue mask = 0) :
    (TlsMpc.Node.Local.Edwards.hints me z mask).isSome := by
  unfold TlsMpc.Node.Local.Edwards.hints
  have := toAffineAll_isSome hinv (TlsMpc.Node.Local.Edwards.windowBases (TlsMpc.Node.Local.Edwards.hintBase me z mask))
    (fun e he => (windowBases_good hX _ (hintBase_on hA me z mask hz hm) e he).z_ne)
  simpa using this

/-- **The public table of a curve point never fails** (F25b for `publicTable`). -/
theorem publicTable_isSome (hinv : FieldInverse) (hX : ExtClosed) (p : TlsMpc.Node.Local.Edwards.Value)
    (hp : curveValue p = 0) : (TlsMpc.Node.Local.Edwards.publicTable p).isSome := by
  unfold TlsMpc.Node.Local.Edwards.publicTable
  have hall := PL.foldl_inv (fun (st : List TlsMpc.Node.Local.Edwards.ExtV × TlsMpc.Node.Local.Edwards.ExtV) =>
      (∀ e ∈ st.1, ExtGood e) ∧ ExtGood st.2)
    (fun (st : List TlsMpc.Node.Local.Edwards.ExtV × TlsMpc.Node.Local.Edwards.ExtV) (_ : Nat) =>
      (st.2 :: st.1, TlsMpc.Node.Local.Edwards.extAdd st.2 st.2))
    (fun st _ h => by
      refine ⟨fun e he => ?_, hX _ _ h.2 h.2⟩
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact h.2
      · exact h.1 e he)
    (List.range 256) ([], TlsMpc.Node.Local.Edwards.ofAffine p) ⟨fun e he => by simp at he, PL.ofAffineValue_good p hp⟩
  have := toAffineAll_isSome hinv _ (fun e he => (hall.1 e (List.mem_reverse.mp he)).z_ne)
  simpa using this

end LL

end TlsMpc.Node.Flows.Curve
