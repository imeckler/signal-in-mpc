import TlsMpcProofs.EdwardsScalarMul
import TlsMpcProofs.X25519Special

/-!
# X25519 from a bit table (`EdwardsHinted.bitSum`) is the clamped scalar multiple

The unsigned instance of the digit lemma: `bitSum` adds the chosen entries `2^(j+3)·P`
(`j < 251`, bit `j` of its input) and `2^254·P`, i.e. `k·P` for
`k = 2²⁵⁴ + 8·Σ cⱼ·2^j` (`bitSum_value`); with the bits of an X25519 scalar that `k` is
`clampedScalar` (`X25519Clamp.clampedScalar_eq`), so the quotient of its two outputs is
`X25519.spec` of the point's `u` (`bitSum_eq_x25519`). The same unsigned sum
(`sum_choose_smul`) gives `prepareHinted`'s initial point: once every link holds it represents
`(kA + kB)·P` for the two parties' 252-bit scalars (`prepareHinted_initial`).
-/

namespace TlsMpcProofs.Ed25519
open TlsMpc Edwards
open FieldDag (F ofNat)
open EdwardsAffine EdwardsHinted

/-- The big-endian value of `f (k−1), …, f 0` as a sum. -/
theorem bitsValue_range (f : ℕ → Bool) : ∀ k : ℕ,
    bitsValue 0 ((List.range k).reverse.map f) = ((List.range k).map (fun j => (f j).toNat * 2 ^ j)).sum
  | 0 => rfl
  | k + 1 => by
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.map_cons, bitsValue_cons, bitsValue_eq, List.length_map, List.length_reverse,
      List.length_range, bitsValue_range f k, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring

/-- A chosen entry is the point or the neutral element. -/
theorem extRep_chooseExtValue (c : Bool) {e : ExtV} {Q : Curve} (h : ExtRep e Q) :
    ExtRep (chooseExtValue (X25519.bitValue c) e) (if c then Q else 0) := by
  cases c
  · have ht : tup (chooseExtValue (X25519.bitValue false) e) = (0, 1, 1, 0) := by
      simp [tup, chooseExtValue, X25519.bitValue, toZMod_zero, toZMod_ofNat_one]
    unfold ExtRep
    rw [ht]
    exact rep4_zero
  · have ht : tup (chooseExtValue (X25519.bitValue true) e) = tup e := by
      simp [tup, chooseExtValue, X25519.bitValue]
    unfold ExtRep
    rw [ht]
    exact h

/-- **Unsigned digits:** chosen multiples sum to the multiple by the digits' value. -/
theorem sum_choose_smul (P : Curve) (c : ℕ → Bool) (e : ℕ → ℕ) (L : List ℕ) :
    (L.map (fun j => if c j then e j • P else 0)).sum =
      (L.map (fun j => (c j).toNat * e j)).sum • P := by
  induction L with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons, ih, add_nsmul]
    cases c a <;> simp

theorem quot_montU {a Z y : K} (hZ : Z ≠ 0) :
    (a + (Z + y * Z - a)) / (Z - y * Z) = (1 + y) / (1 - y) := by
  rw [show a + (Z + y * Z - a) = Z * (1 + y) by ring, show Z - y * Z = Z * (1 - y) by ring,
    mul_div_mul_left _ _ hZ]

/-- The list `bitSum` sums: the chosen points `2^(j+3)·P`, then `2^254·P`. -/
def bitSumList : List ExtE :=
  (List.range agreementBits).map (fun j => chooseExt (.input (2 + 4 * (agreementBits + 1) + j))
    (extInput (2 + 4 * j))) ++ [extInput (2 + 4 * agreementBits)]

theorem bitSum_eval (input : ℕ → F) :
    (bitSum ()).map (FieldDag.Expr.eval input) =
      [input 1 + input 0 * ((evalExt input (extSum bitSumList)).z +
          (evalExt input (extSum bitSumList)).y - input 1),
        (evalExt input (extSum bitSumList)).z - (evalExt input (extSum bitSumList)).y] := by
  simp only [bitSum, bitSumList, List.map_cons, List.map_nil, FieldDag.Expr.eval,
    FieldDag.Bin.eval, EdwardsAffine.add, EdwardsAffine.sub, EdwardsAffine.mul, evalExt]

/-- **`bitSum` computes `u(k·P)`:** if input point `j` (`j ≤ 251`, inputs `2 + 4j …`) represents
`2^(j+3)·P`, scalar input `j < 251` is the bit `c j` and `valid = 1`, the two outputs `N`, `D` have
`N/D = montU (k·P)` for `k = 2²⁵⁴ + 8·(value of c 250 … c 0)`. -/
theorem bitSum_value (input : ℕ → F) {P : Curve} (c : ℕ → Bool)
    (hpts : ∀ j ≤ agreementBits, ExtRep (evalExt input (extInput (2 + 4 * j))) (2 ^ (j + 3) • P))
    (hbits : ∀ j < agreementBits, input (2 + 4 * (agreementBits + 1) + j) = X25519.bitValue (c j))
    (hvalid : input 0 = ofNat 1) :
    ∃ N D : F, (bitSum ()).map (FieldDag.Expr.eval input) = [N, D] ∧
      toZMod N / toZMod D =
        montU ((2 ^ 254 + 8 * bitsValue 0 ((List.range agreementBits).reverse.map c)) • P) := by
  rw [bitSum_eval]
  refine ⟨_, _, rfl, ?_⟩
  let l : List (ExtV × Curve) :=
    (List.range agreementBits).map (fun j =>
      (chooseExtValue (X25519.bitValue (c j)) (evalExt input (extInput (2 + 4 * j))),
        if c j then 2 ^ (j + 3) • P else 0)) ++
      [(evalExt input (extInput (2 + 4 * agreementBits)), 2 ^ (agreementBits + 3) • P)]
  have hl : ∀ a ∈ l, ExtRep a.1 a.2 := by
    intro a ha
    simp only [l, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at ha
    rcases ha with ⟨j, hj, rfl⟩ | rfl
    · exact extRep_chooseExtValue (c j) (hpts j hj.le)
    · exact hpts agreementBits le_rfl
  have hS := extRep_extSumValue l hl
  have e1 : l.map Prod.fst = bitSumList.map (evalExt input) := by
    simp only [l, bitSumList, List.map_append, List.map_map, List.map_cons, List.map_nil]
    refine congrArg₂ (· ++ ·) (List.map_congr_left fun j hj => ?_) rfl
    show chooseExtValue (X25519.bitValue (c j)) (evalExt input (extInput (2 + 4 * j))) =
      chooseExtValue (input (2 + 4 * (agreementBits + 1) + j)) (evalExt input (extInput (2 + 4 * j)))
    rw [hbits j (List.mem_range.mp hj)]
  have hX : ((List.range agreementBits).map (fun j => (c j).toNat * 2 ^ (j + 3))).sum =
      8 * ((List.range agreementBits).map (fun j => (c j).toNat * 2 ^ j)).sum := by
    rw [← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro j _
    ring
  have e2 : (l.map Prod.snd).sum =
      (2 ^ 254 + 8 * bitsValue 0 ((List.range agreementBits).reverse.map c)) • P := by
    simp only [l, List.map_append, List.map_map, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, add_zero, Function.comp_def]
    rw [sum_choose_smul, ← add_nsmul, bitsValue_range, hX, show agreementBits + 3 = 254 from rfl,
      add_comm]
  rw [e1, e2, ← extSum_eval] at hS
  obtain ⟨hz, -, hy, -⟩ := hS
  rw [hvalid]
  simp only [toZMod_add, toZMod_mul, toZMod_sub, toZMod_ofNat_one, one_mul]
  simp only [tup] at hz hy
  rw [hy, montU]
  exact quot_montU hz

/-- **`bitSum` with the bits of an X25519 scalar computes X25519:** if the table holds
`2^i·P` for the curve point `P` with Montgomery representative `u` and the scalar inputs are bits
3 … 253 of `input'`, the quotient of the outputs is `X25519.spec input' u`. -/
theorem bitSum_eq_x25519 (input : ℕ → F) (input' : ℕ → Bool) (u : F) {P : Curve}
    (hP : MRep (toZMod u) 1 P)
    (hpts : ∀ j ≤ agreementBits, ExtRep (evalExt input (extInput (2 + 4 * j))) (2 ^ (j + 3) • P))
    (hbits : ∀ j < agreementBits,
      input (2 + 4 * (agreementBits + 1) + j) = X25519.bitValue (input' (j + 3)))
    (hvalid : input 0 = ofNat 1) :
    ∃ N D : F, (bitSum ()).map (FieldDag.Expr.eval input) = [N, D] ∧
      toZMod N / toZMod D = toZMod (X25519.spec input' u) := by
  obtain ⟨N, D, h, hq⟩ := bitSum_value input (fun j => input' (j + 3)) hpts hbits hvalid
  refine ⟨N, D, h, ?_⟩
  rw [hq, spec_eq_montU' input' u P hP, clampedScalar_eq]
  rfl

/-- A chosen affine entry (`chooseAffine`) is the point or the neutral element. -/
theorem extRep_chooseAffine (input : ℕ → F) (bit : FieldDag.Expr) (p : EdwardsAffine.Point)
    (c : Bool) (hb : bit.eval input = X25519.bitValue c) {Q : Curve}
    (hp : Affine (evalPoint input p) Q) :
    ExtRep (evalExt input (chooseAffine bit p)) (if c then Q else 0) := by
  have he : evalExt input (chooseAffine bit p) =
      ⟨bit.eval input * p.1.eval input, ofNat 1 + bit.eval input * (p.2.eval input - ofNat 1),
        ofNat 1, bit.eval input * p.1.eval input * p.2.eval input⟩ := by
    simp only [evalExt, chooseAffine, FieldDag.Expr.eval, FieldDag.Bin.eval, EdwardsAffine.mul,
      EdwardsAffine.add, EdwardsAffine.sub]
  rw [he, hb]
  cases c
  · have ht : tup (⟨X25519.bitValue false * p.1.eval input,
        ofNat 1 + X25519.bitValue false * (p.2.eval input - ofNat 1), ofNat 1,
        X25519.bitValue false * p.1.eval input * p.2.eval input⟩ : ExtV) = (0, 1, 1, 0) := by
      simp [tup, X25519.bitValue, toZMod_zero, toZMod_ofNat_one]
    unfold ExtRep
    rw [ht]
    exact rep4_zero
  · have h1 := extRep_ofAffineValue hp
    have ht : tup (⟨X25519.bitValue true * p.1.eval input,
        ofNat 1 + X25519.bitValue true * (p.2.eval input - ofNat 1), ofNat 1,
        X25519.bitValue true * p.1.eval input * p.2.eval input⟩ : ExtV) =
        tup (ofAffineValue (evalPoint input p)) := by
      simp [tup, X25519.bitValue, ofAffineValue, evalPoint]
    unfold ExtRep at h1 ⊢
    rw [ht]
    exact h1

/-- **`prepareHinted`'s initial point is `(kA + kB)·P`:** once every link holds (`P` the curve
point at inputs 0, 1), the balanced sum of the chosen table entries (`chooseAffine` of bit `i`
and `bitEntry (i mod 252)`, `i < 504`) represents `(kA + kB)·P`, `kA` the value of bits
0 … 251 and `kB` of bits 252 … 503 (little-endian, `c i` the bit at input `prepareBits + i`). -/
theorem prepareHinted_initial (input : ℕ → F) {P : Curve} (hP : Affine (input 0, input 1) P)
    (h : LinkedFrom (evalPoint input) window (inputPoint 0)
      ((List.range (windows - 1)).map (fun i => hinted (prepareHints + 4 * i))))
    (c : ℕ → Bool) (hbits : ∀ i < 2 * scalarBits, input (prepareBits + i) = X25519.bitValue (c i)) :
    ExtRep (evalExt input (extSum ((List.range (2 * scalarBits)).map (fun i =>
        chooseAffine (.input (prepareBits + i))
          (bitEntry (entries window (prepareBases ())) (i % scalarBits))))))
      ((bitsValue 0 ((List.range 252).reverse.map c) +
        bitsValue 0 ((List.range 252).reverse.map (fun i => c (252 + i)))) • P) := by
  let l : List (ExtV × Curve) := (List.range (2 * scalarBits)).map (fun i =>
    (evalExt input (chooseAffine (.input (prepareBits + i))
      (bitEntry (entries window (prepareBases ())) (i % scalarBits))),
     if c i then 2 ^ (i % 252) • P else 0))
  have hl : ∀ a ∈ l, ExtRep a.1 a.2 := by
    intro a ha
    simp only [l, List.mem_map, List.mem_range] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    exact extRep_chooseAffine input (FieldDag.Expr.input (prepareBits + i)) _ (c i) (hbits i hi)
      (prepareHinted_bitEntry input hP h (i % scalarBits)
        (by have : i % scalarBits < scalarBits := Nat.mod_lt _ (by decide)
            simp only [scalarBits] at this ⊢; omega))
  have hS := extRep_extSumValue l hl
  have e1 : l.map Prod.fst = ((List.range (2 * scalarBits)).map (fun i =>
      chooseAffine (.input (prepareBits + i))
        (bitEntry (entries window (prepareBases ())) (i % scalarBits)))).map (evalExt input) := by
    simp only [l, List.map_map]
    rfl
  have e2 : (l.map Prod.snd).sum = ((List.range 252).map (fun i => (c i).toNat * 2 ^ i) ++
      (List.range 252).map (fun i => (c (252 + i)).toNat * 2 ^ i)).sum • P := by
    simp only [l, List.map_map, Function.comp_def]
    rw [sum_choose_smul, show 2 * scalarBits = 252 + 252 from rfl, List.range_add, List.map_append,
      List.map_map]
    have hA : (List.range 252).map (fun j => (c j).toNat * 2 ^ (j % 252)) =
        (List.range 252).map (fun i => (c i).toNat * 2 ^ i) :=
      List.map_congr_left (fun i hi => by rw [Nat.mod_eq_of_lt (List.mem_range.mp hi)])
    have hB : (List.range 252).map ((fun j => (c j).toNat * 2 ^ (j % 252)) ∘ fun x => 252 + x) =
        (List.range 252).map (fun i => (c (252 + i)).toNat * 2 ^ i) :=
      List.map_congr_left (fun i hi => by
        have hi' := List.mem_range.mp hi
        simp only [Function.comp_apply]
        rw [show (252 + i) % 252 = i by omega])
    rw [hA, hB]
  rw [e1, e2, ← extSum_eval, List.sum_append, ← bitsValue_range, ← bitsValue_range] at hS
  exact hS

end TlsMpcProofs.Ed25519
