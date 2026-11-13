import TlsMpc.Node.Flows.Masks

/-!
# P-CUT: the protocol layer (what is opened, what is checked, as functions of the candidates)

REORGANIZATION_PLAN.md 7.1 P-CUT (a)–(g), stage S10. The run-level link (that the replies a party
gets are these functions of the values in the engines) is in `MasksRun.lean`.

THE CANDIDATES. `Vals`: for owner `o` (0: A, 1: B) and candidate index `c`, the 255 bits `bits o c`
input to the Boolean engine and the element `elem o c` input to the field engine. Inputs are
independent per engine, so a cheating party may make them inconsistent: its ERROR is
`err o c = (val(bits) − elem) mod p` (plan 7.1). A candidate is CANONICAL when `val(bits) < p`.

PROVED (all on `Nat`/`F` arithmetic and the circuit specifications of `ConvertBase.lean`; no
hypothesis about the engines):
  * (d) `cutCheck_iff`: the cut check on the opened values passes iff every cut candidate of both
    owners is canonical and has error 0. `err_zero_iff`: for canonical values, error 0 is equality
    of the two values.
  * (e) `bucketOk_iff`: for a canonical reference, the check of (reference, member) passes iff
    `val(ref) + val(member) < 2p` and the errors cancel, `err ref + err member ≡ 0 (mod p)`; for
    canonical members just the latter (`bucketOk_iff_canonical`). `bucketCheck_iff`: the whole
    bucket check is the conjunction over the pairs. Corollaries (the detection rule the Mathlib
    counting model assumes): `bucket_mixed_fails` (a reference and a member of which exactly one
    has error 0 fail), `bucket_survivor` (a reference with error e ≠ 0 passes with a member only if
    the member's error is −e).
  * (f) `finalizeMask_flag`, `finalizeBits_flag`: the flag opened per kept reference is "both
    canonical" (word masks), resp. "both canonical and both at least 32" (bit blocks), and
    `flagsOk_iff`: the flag check passes iff every flag is set.
  * (g) `bitBlock_unique` (with `FieldInverse`): field inputs c₀ … c₂₅₄ whose bit checks are 0 and
    whose recomposition equals the reference's field value `v`, with `val(b) = v` and
    `19 ≤ val(b) < p`, are exactly the bits of `b`. `bitCheck_zero_iff`: a bit check is 0 iff the
    input is 0 or 1 (the converse of `FieldBits.bitCheck_bit`, P-BITS (a)).
  * (a) `honest_*`: honest candidates (canonical random r as bits and as element) pass the cut, the
    buckets and the flags, the word mask is (word (r_A + r_B mod p), r_A + r_B) with
    val(word) = the field value, and a bit pair's field value is the bit of the XOR
    (`honest_mask`, `honest_pair`).
  * (c) `hiding_releases`: the values released (cut words, bucket sums in both engines, flags, and
    the honest party's bit-block checks) are unchanged when the honest party's candidates are
    shifted by `d` with `d ≡ 0` on the cut and `d(ref) + d(member) ≡ 0 (mod p)` in every bucket;
    `shift_shift` (the shift by d then by p − d is the identity: a bijection on the honest party's
    candidate values), `shift_ref` (the kept reference becomes `ref + d(ref) mod p`, so any target
    canonical value is reached).
-/

namespace TlsMpc.Node.Flows.Masks

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Conv
open TlsMpc.FieldDag (F modulus)

/-! ## Arithmetic helpers -/

theorem P_pos : 0 < P := by decide

theorem fval_lt (x : F) : x.val < P := by
  rw [P_modulus]
  exact x.isLt

theorem mod_modulus (n : Nat) : n % modulus = n % P := by rw [P_modulus]

theorem fadd_val (x y : F) : (x + y).val = (x.val + y.val) % P := by
  rw [Fin.val_add, mod_modulus]

theorem ofNat_val (n : Nat) : (TlsMpc.FieldDag.ofNat n).val = n % P := by
  show (Fin.ofNat modulus n).val = n % P
  rw [Fin.val_ofNat, mod_modulus]

/-! ## Words of a flat list -/

theorem chunksN_flatten (w : Nat) : ∀ (ws : List Bits), (∀ x ∈ ws, x.length = w) →
    chunksN w ws.length ws.flatten = ws
  | [], _ => rfl
  | x :: ws, h => by
    have hx := h x (by simp)
    simp only [List.length_cons, chunksN, List.flatten_cons]
    rw [List.take_left' hx, List.drop_left' hx, chunksN_flatten w ws (fun y hy => h y (by simp [hy]))]

theorem chunks_flatten (w : Nat) (hw : 0 < w) (ws : List Bits) (h : ∀ x ∈ ws, x.length = w) :
    chunks w ws.flatten = ws := by
  have hl : ws.flatten.length = w * ws.length := by
    rw [List.length_flatten]
    clear hw
    induction ws with
    | nil => simp
    | cons y ws ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [h y (by simp), ih (fun z hz => h z (by simp [hz]))]
      rw [Nat.mul_succ, Nat.add_comm]
  unfold chunks
  rw [hl, Nat.mul_div_cancel_left _ hw]
  exact chunksN_flatten w ws h

theorem zip_fst_snd {α β : Type} (l : List (α × β)) : (l.map Prod.fst).zip (l.map Prod.snd) = l := by
  induction l with
  | nil => rfl
  | cons e l ih => simp [ih]

/-- The words check on a list of (word, element) pairs: all match. -/
theorem wordsMatch_pairs (canon : Bool) (l : List (Bits × F)) :
    wordsMatch canon (l.map Prod.fst) (l.map Prod.snd) =
      l.all fun e => (!canon || decide (natOf e.1 < P)) && natOf e.1 == e.2.val := by
  simp [wordsMatch, zip_fst_snd]

/-! ## Candidates -/

/-- The candidates' values in the two engines. -/
structure Vals where
  bits : Nat → Nat → Bits
  elem : Nat → Nat → F

namespace Vals

variable (x : Vals)

def val (o c : Nat) : Nat := natOf (x.bits o c)
/-- The error `(val(bits) − elem) mod p`. -/
def err (o c : Nat) : Nat := (x.val o c + (P - (x.elem o c).val)) % P
/-- Every candidate has 255 bits (true of every model run: the input has M·255 bits). -/
def Wide : Prop := ∀ o c, (x.bits o c).length = W

end Vals

/-- For canonical values, error 0 is equality. -/
theorem err_zero_iff (x : Vals) (o c : Nat) (h : x.val o c < P) : x.err o c = 0 ↔ x.val o c = (x.elem o c).val := by
  have he := fval_lt (x.elem o c)
  unfold Vals.err
  generalize x.val o c = v at h ⊢
  generalize (x.elem o c).val = e at he ⊢
  rw [P_eq] at *
  omega

/-! ## (d) The cut -/

/-- What the cut opens: per owner, per cut candidate, its word and its element. -/
def cutRel (x : Vals) (cut : List Nat) : List (Bits × F) :=
  owners.flatMap fun o => cut.map fun c => (x.bits o c, x.elem o c)

/-- **P-CUT (d).** The cut check on the opened values (the Boolean words concatenated, the
elements in the same order) passes iff every cut candidate of both owners is canonical and has
error 0. -/
theorem cutCheck_iff (x : Vals) (hw : x.Wide) (cut : List Nat) :
    cutCheck ((cutRel x cut).map Prod.fst).flatten ((cutRel x cut).map Prod.snd) = true ↔
      ∀ o ∈ owners, ∀ c ∈ cut, x.val o c < P ∧ x.err o c = 0 := by
  have hc : chunks W ((cutRel x cut).map Prod.fst).flatten = (cutRel x cut).map Prod.fst := by
    apply chunks_flatten W (by decide)
    intro y hy
    simp only [cutRel, List.mem_map, List.mem_flatMap] at hy
    obtain ⟨e, ⟨o, -, c, -, rfl⟩, rfl⟩ := hy
    exact hw o c
  unfold cutCheck
  rw [hc, wordsMatch_pairs, List.all_eq_true]
  constructor
  · intro h o ho c hcut
    have := h (x.bits o c, x.elem o c) (by simp only [cutRel, List.mem_flatMap, List.mem_map]; exact ⟨o, ho, c, hcut, rfl⟩)
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact ⟨this.1, (err_zero_iff x o c this.1).mpr this.2⟩
  · intro h e he
    simp only [cutRel, List.mem_flatMap, List.mem_map] at he
    obtain ⟨o, ho, c, hcut, rfl⟩ := he
    obtain ⟨h1, h2⟩ := h o ho c hcut
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨h1, (err_zero_iff x o c h1).mp h2⟩

/-! ## (e) The buckets -/

/-- The check of (reference r, member m) of one owner: the opened `modAdd` word equals the opened
field sum. -/
def bucketOk (vr vm : Nat) (er em : F) : Bool := natOf (word (addModSpec vr vm)) == (er + em).val

/-- The common error arithmetic: for `vr < p` and `vm < 2²⁵⁵`. -/
theorem bucketOk_iff (vr vm : Nat) (er em : F) (hr : vr < P) (hm : vm < 2 ^ 255) :
    bucketOk vr vm er em = true ↔
      vr + vm < 2 * P ∧ ((vr + (P - er.val)) % P + (vm + (P - em.val)) % P) % P = 0 := by
  have h1 := fval_lt er
  have h2 := fval_lt em
  unfold bucketOk
  rw [fadd_val, beq_iff_eq, word, natOf_bitsOfNat]
  unfold addModSpec
  rw [two_pow_eq] at hm ⊢
  generalize er.val = a at h1 ⊢
  generalize em.val = b at h2 ⊢
  rw [P_eq] at *
  split <;> omega

/-- For canonical members: the check passes iff the errors cancel mod p. -/
theorem bucketOk_iff_canonical (x : Vals) (o r m : Nat) (hr : x.val o r < P) (hm : x.val o m < P) :
    bucketOk (x.val o r) (x.val o m) (x.elem o r) (x.elem o m) = true ↔ (x.err o r + x.err o m) % P = 0 := by
  rw [bucketOk_iff _ _ _ _ hr (by have := P_lt_two_pow; omega)]
  unfold Vals.err
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨by omega, h⟩

/-- **The detection rule the counting model assumes** (proofs/ `CutAndChoose`: "a bucket that mixes
good and bad candidates aborts"): with a canonical reference, a reference and a member of which
exactly one has error 0 fail the check. -/
theorem bucket_mixed_fails (x : Vals) (o r m : Nat) (hr : x.val o r < P) (hm : x.val o m < 2 ^ 255)
    (hmix : (x.err o r = 0 ∧ x.err o m ≠ 0) ∨ (x.err o r ≠ 0 ∧ x.err o m = 0)) :
    bucketOk (x.val o r) (x.val o m) (x.elem o r) (x.elem o m) = false := by
  have he1 : x.err o r < P := Nat.mod_lt _ P_pos
  have he2 : x.err o m < P := Nat.mod_lt _ P_pos
  cases hb : bucketOk (x.val o r) (x.val o m) (x.elem o r) (x.elem o m) with
  | false => rfl
  | true =>
    obtain ⟨-, h⟩ := (bucketOk_iff _ _ _ _ hr hm).mp hb
    have : (x.err o r + x.err o m) % P = 0 := h
    rw [P_eq] at this he1 he2
    rcases hmix with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- **A surviving bad reference** (P-CUT (e), corollary): a reference with error e ≠ 0 passes the
check with a member only if the member's error is p − e (that is, −e mod p). -/
theorem bucket_survivor (x : Vals) (o r m : Nat) (hr : x.val o r < P) (hm : x.val o m < 2 ^ 255)
    (he : x.err o r ≠ 0) (hb : bucketOk (x.val o r) (x.val o m) (x.elem o r) (x.elem o m) = true) :
    x.err o m = P - x.err o r := by
  have he1 : x.err o r < P := Nat.mod_lt _ P_pos
  have he2 : x.err o m < P := Nat.mod_lt _ P_pos
  obtain ⟨-, h⟩ := (bucketOk_iff _ _ _ _ hr hm).mp hb
  have : (x.err o r + x.err o m) % P = 0 := h
  rw [P_eq] at this he1 he2 ⊢
  omega

/-- What the buckets open: per (owner, bucket j, member k), the `modAdd` word and the field sum. -/
def bucketRel (x : Vals) (mem : Nat → Nat → Nat) (ps : List (Nat × Nat × Nat)) : List (Bits × F) :=
  ps.map fun e => (word (addModSpec (x.val e.1 (mem e.2.1 0)) (x.val e.1 (mem e.2.1 e.2.2))),
    x.elem e.1 (mem e.2.1 0) + x.elem e.1 (mem e.2.1 e.2.2))

/-- **P-CUT (e), the whole bucket check**: it passes iff every pair passes. -/
theorem bucketCheck_iff (x : Vals) (mem : Nat → Nat → Nat) (ps : List (Nat × Nat × Nat)) :
    bucketCheck ((bucketRel x mem ps).map Prod.fst).flatten ((bucketRel x mem ps).map Prod.snd) = true ↔
      ∀ e ∈ ps, bucketOk (x.val e.1 (mem e.2.1 0)) (x.val e.1 (mem e.2.1 e.2.2))
        (x.elem e.1 (mem e.2.1 0)) (x.elem e.1 (mem e.2.1 e.2.2)) = true := by
  have hc : chunks W ((bucketRel x mem ps).map Prod.fst).flatten = (bucketRel x mem ps).map Prod.fst := by
    apply chunks_flatten W (by decide)
    intro y hy
    simp only [bucketRel, List.map_map, List.mem_map, Function.comp_def] at hy
    obtain ⟨e, -, rfl⟩ := hy
    exact length_word _
  unfold bucketCheck
  rw [hc, wordsMatch_pairs, List.all_eq_true, bucketRel, List.forall_mem_map]
  simp only [Bool.not_false, Bool.true_or, Bool.true_and]
  exact Iff.rfl

/-! ## (f) The flags -/

/-- The flag of `finalize-mask` on a reference pair: both canonical. -/
theorem finalizeMask_flag (a b : Bits) (ha : a.length = W) (hb : b.length = W) :
    (finalizeMaskEval (a ++ b)).getD 255 false = (decide (natOf a < P) && decide (natOf b < P)) := by
  have hx : wordX (a ++ b) = natOf a := by simp [wordX, List.take_left' ha]
  have hy : wordY (a ++ b) = natOf b := by simp [wordY, List.drop_left' ha, List.take_of_length_le (Nat.le_of_eq hb)]
  simp only [finalizeMaskEval, modaddEval, hx, hy]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_of_eq (length_word _)), length_word]
  rfl

/-- The flag of `finalize-bits`: both canonical and both at least 32. -/
theorem finalizeBits_flag (a b : Bits) (ha : a.length = W) (hb : b.length = W) :
    (finalizeBitsEval (a ++ b)).getD 255 false =
      (decide (natOf a < P) && decide (natOf b < P) && decide (32 ≤ natOf a) && decide (32 ≤ natOf b)) := by
  have hx : wordX (a ++ b) = natOf a := by simp [wordX, List.take_left' ha]
  have hy : wordY (a ++ b) = natOf b := by simp [wordY, List.drop_left' ha, List.take_of_length_le (Nat.le_of_eq hb)]
  have hl : (List.zipWith (· ^^ ·) ((a ++ b).take 255) (((a ++ b).drop 255).take 255)).length = 255 := by
    simp [List.take_left' ha, List.drop_left' ha, List.take_of_length_le (Nat.le_of_eq hb), ha, hb]
  simp only [finalizeBitsEval, hx, hy]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hl]
  rfl

/-- The bits of `finalize-bits`: the XOR of the two references. -/
theorem finalizeBits_word (a b : Bits) (ha : a.length = W) (hb : b.length = W) :
    (finalizeBitsEval (a ++ b)).take 255 = List.zipWith (· ^^ ·) a b := by
  have hl : (List.zipWith (· ^^ ·) a b).length = 255 := by simp [ha, hb]
  simp only [finalizeBitsEval, List.take_left' ha, List.drop_left' ha,
    List.take_of_length_le (Nat.le_of_eq hb)]
  rw [List.take_left' hl]

/-- The word of `finalize-mask`: `modAdd` of the two references. -/
theorem finalizeMask_word (a b : Bits) (ha : a.length = W) (hb : b.length = W) :
    (finalizeMaskEval (a ++ b)).take 255 = word (addModSpec (natOf a) (natOf b)) := by
  have hx : wordX (a ++ b) = natOf a := by simp [wordX, List.take_left' ha]
  have hy : wordY (a ++ b) = natOf b := by simp [wordY, List.drop_left' ha, List.take_of_length_le (Nat.le_of_eq hb)]
  simp only [finalizeMaskEval, modaddEval, hx, hy]
  rw [List.take_left' (length_word _)]

/-- **P-CUT (f), the flag check**: it passes iff every flag is set. -/
theorem flagsOk_iff (fl : Bits) : fl.all id = true ↔ ∀ x ∈ fl, x = true := by
  simp [List.all_eq_true]

/-! ## (g) Bit blocks -/

open TlsMpc.FieldDag.V3 (FieldInverse) in
/-- **P-BITS (a), the converse of `FieldBits.bitCheck_bit`** (with `FieldInverse`: no zero
divisors): `c·(c − 1) = 0` iff `c` is 0 or 1. -/
theorem bitCheck_zero_iff (hinv : FieldInverse) (c : F) :
    c * (c - TlsMpc.FieldDag.ofNat 1) = 0 ↔ c = 0 ∨ c = TlsMpc.FieldDag.ofNat 1 := by
  constructor
  · intro h
    rcases (TlsMpc.FieldDag.V3.opening_zero_iff hinv c (c - TlsMpc.FieldDag.ofNat 1)).mp h with h | h
    · exact Or.inl h
    · right
      grind
  · rintro (h | h) <;> subst h <;> grind

theorem bitValue_val (b : Bool) : (X25519.bitValue b).val = b.toNat := by
  cases b <;> rfl

/-- `hornerValue` of bits is the value of the bits, mod p. -/
theorem horner_bits (bs : Bits) :
    TlsMpc.FieldBits.hornerValue (bs.map X25519.bitValue) = TlsMpc.FieldDag.ofNat (natOf bs) := by
  induction bs with
  | nil => rfl
  | cons x bs ih =>
    simp only [List.map_cons, TlsMpc.FieldBits.hornerValue, ih, natOf]
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_mul, mod_modulus, ofNat_val, bitValue_val]
    have := Bool.toNat_le x
    generalize natOf bs = n
    rw [P_eq]
    omega

/-- A bit vector of field values: every entry 0 or 1. -/
theorem bits_of_zero_one (cs : List F) (h : ∀ c ∈ cs, c = 0 ∨ c = TlsMpc.FieldDag.ofNat 1) :
    ∃ bs : Bits, cs = bs.map X25519.bitValue := by
  induction cs with
  | nil => exact ⟨[], rfl⟩
  | cons c cs ih =>
    obtain ⟨bs, hbs⟩ := ih (fun y hy => h y (by simp [hy]))
    rcases h c (by simp) with hc | hc
    · exact ⟨false :: bs, by rw [hc, hbs]; rfl⟩
    · exact ⟨true :: bs, by rw [hc, hbs]; rfl⟩

open TlsMpc.FieldDag.V3 (FieldInverse) in
/-- **P-CUT (g).** Field inputs `cs` (255 of them) whose bit checks are all 0 and whose
recomposition equals the reference's field value `v`, where `v` is the value of the reference's
Boolean bits `b` (`val(b) = v`, error 0) and `19 ≤ val(b) < p`: then `cs` are the bits of `b`
(the uniqueness of the binary representation below 2²⁵⁵; the code requires `val(b) ≥ 32`). -/
theorem bitBlock_unique (hinv : FieldInverse) (cs : List F) (b : Bits) (v : F)
    (hl : cs.length = 255) (hb : b.length = 255)
    (hcheck : ∀ c ∈ cs, c * (c - TlsMpc.FieldDag.ofNat 1) = 0)
    (hrec : TlsMpc.FieldBits.hornerValue cs - v = 0)
    (hv : v.val = natOf b) (h19 : 19 ≤ natOf b) (hP : natOf b < P) :
    cs = b.map X25519.bitValue := by
  obtain ⟨bs, rfl⟩ := bits_of_zero_one cs (fun c hc => (bitCheck_zero_iff hinv c).mp (hcheck c hc))
  have hbl : bs.length = 255 := by simpa using hl
  have hrec' : TlsMpc.FieldBits.hornerValue (bs.map X25519.bitValue) = v := by
    have : TlsMpc.FieldBits.hornerValue (bs.map X25519.bitValue) - v + v = 0 + v := by rw [hrec]
    grind
  rw [horner_bits] at hrec'
  have hval := congrArg Fin.val hrec'
  rw [ofNat_val, hv] at hval
  have hlt := natOf_lt bs
  rw [hbl, two_pow_eq] at hlt
  have heq : natOf bs = natOf b := by
    by_cases hs : natOf bs < P
    · rw [Nat.mod_eq_of_lt hs] at hval
      exact hval
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hval
      omega
  rw [natOf_inj (by rw [hbl, hb]) heq]

/-! ## (a) Honest candidates -/

/-- An honest candidate: a canonical random `r`, as 255 bits and as the element `r`. -/
def honest (r : Nat) : Bits × F := (word r, TlsMpc.FieldDag.ofNat r)

theorem honest_val (r : Nat) (hr : r < P) : natOf (honest r).1 = r := natOf_word r (by have := P_lt_two_pow; omega)

theorem honest_elem (r : Nat) (hr : r < P) : (honest r).2.val = r := by
  simp only [honest]
  rw [ofNat_val, Nat.mod_eq_of_lt hr]

/-- **P-CUT (a), checks.** An honest candidate is canonical with error 0, so it passes the cut
(`cutCheck_iff`) and every bucket check with honest partners (`bucketOk_iff_canonical`). -/
theorem honest_ok (x : Vals) (o c r : Nat) (hr : r < P) (hx : x.bits o c = (honest r).1)
    (he : x.elem o c = (honest r).2) : x.val o c < P ∧ x.err o c = 0 := by
  have h1 : x.val o c = r := by rw [Vals.val, hx, honest_val r hr]
  refine ⟨by rw [h1]; exact hr, (err_zero_iff x o c (by rw [h1]; exact hr)).mpr ?_⟩
  rw [h1, he, honest_elem r hr]

/-- **P-CUT (a), word masks.** From honest references r_A, r_B: the mask's word is
`(r_A + r_B) mod p`, its field element is `r_A + r_B`, and `val(word) = f`. -/
theorem honest_mask (rA rB : Nat) (hA : rA < P) (hB : rB < P) :
    (finalizeMaskEval ((honest rA).1 ++ (honest rB).1)).take 255 = word ((rA + rB) % P) ∧
      natOf (word ((rA + rB) % P)) = ((honest rA).2 + (honest rB).2).val ∧
      (finalizeMaskEval ((honest rA).1 ++ (honest rB).1)).getD 255 false = true := by
  have hla : (honest rA).1.length = W := length_word _
  have hlb : (honest rB).1.length = W := length_word _
  refine ⟨?_, ?_, ?_⟩
  · rw [finalizeMask_word _ _ hla hlb, honest_val rA hA, honest_val rB hB, addModSpec_canonical _ _ hA hB]
  · rw [natOf_word _ (by have := Nat.mod_lt (rA + rB) P_pos; have := P_lt_two_pow; omega), fadd_val,
      honest_elem rA hA, honest_elem rB hB]
  · rw [finalizeMask_flag _ _ hla hlb, honest_val rA hA, honest_val rB hB]
    simp [hA, hB]

/-- **P-CUT (a), bit pairs.** From honest references at least 32: the flag is set, the Boolean bit
`i` is `bit_i(r_A) ⊕ bit_i(r_B)`, and the field XOR of the parties' coins (the bits of their
references) is that bit. -/
theorem honest_pair (rA rB : Nat) (hA : rA < P) (hB : rB < P) (hA32 : 32 ≤ rA) (hB32 : 32 ≤ rB) (i : Nat)
    (hi : i < 255) :
    (finalizeBitsEval ((honest rA).1 ++ (honest rB).1)).getD 255 false = true ∧
      (finalizeBitsEval ((honest rA).1 ++ (honest rB).1)).getD i false =
        ((honest rA).1.getD i false ^^ (honest rB).1.getD i false) ∧
      bitXorValue (X25519.bitValue ((honest rA).1.getD i false)) (X25519.bitValue ((honest rB).1.getD i false)) =
        X25519.bitValue ((honest rA).1.getD i false ^^ (honest rB).1.getD i false) := by
  have hla : (honest rA).1.length = W := length_word _
  have hlb : (honest rB).1.length = W := length_word _
  refine ⟨?_, ?_, bitXorValue_bits _ _⟩
  · rw [finalizeBits_flag _ _ hla hlb, honest_val rA hA, honest_val rB hB]
    simp [hA, hB, hA32, hB32]
  · have h := finalizeBits_word _ _ hla hlb
    have e : (finalizeBitsEval ((honest rA).1 ++ (honest rB).1)).getD i false =
        ((finalizeBitsEval ((honest rA).1 ++ (honest rB).1)).take 255).getD i false := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]
    rw [e, h, List.getD_eq_getElem?_getD, List.getElem?_zipWith]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by rw [hla]; exact hi), List.getElem?_eq_getElem (by rw [hlb]; exact hi)]
    rfl

/-! ## (c) Hiding: the shift of the honest party's candidates -/

/-- Shift owner `oH`'s candidates by `d c` (mod p), in both engines alike. -/
def shift (x : Vals) (oH : Nat) (d : Nat → Nat) : Vals where
  bits o c := if o = oH then word ((x.val o c + d c) % P) else x.bits o c
  elem o c := if o = oH then x.elem o c + TlsMpc.FieldDag.ofNat (d c) else x.elem o c

/-- The honest party's candidates are canonical, consistent and 255 bits wide. -/
def HonestAt (x : Vals) (oH : Nat) : Prop :=
  ∀ c, (x.bits oH c).length = W ∧ x.val oH c < P ∧ x.val oH c = (x.elem oH c).val

theorem shift_val (x : Vals) (oH : Nat) (d : Nat → Nat) (c : Nat) :
    (shift x oH d).val oH c = (x.val oH c + d c) % P := by
  simp only [Vals.val, shift, if_true]
  rw [natOf_word _ (by have := Nat.mod_lt (natOf (x.bits oH c) + d c) P_pos; have := P_lt_two_pow; omega)]

theorem shift_elem_val (x : Vals) (oH : Nat) (d : Nat → Nat) (c : Nat) :
    ((shift x oH d).elem oH c).val = ((x.elem oH c).val + d c) % P := by
  simp only [shift, if_true]
  rw [fadd_val, ofNat_val, Nat.add_mod_mod]

theorem shift_other (x : Vals) (oH : Nat) (d : Nat → Nat) (o c : Nat) (h : o ≠ oH) :
    (shift x oH d).bits o c = x.bits o c ∧ (shift x oH d).elem o c = x.elem o c := by
  simp [shift, h]

/-- The shift keeps the honest party honest. -/
theorem shift_honest (x : Vals) (oH : Nat) (d : Nat → Nat) (h : HonestAt x oH) : HonestAt (shift x oH d) oH := by
  intro c
  refine ⟨by simp [shift], ?_, ?_⟩
  · rw [shift_val]; exact Nat.mod_lt _ P_pos
  · rw [shift_val, shift_elem_val, (h c).2.2]

/-- **The shift is a bijection on the honest party's candidate values**: shifting by `d`, then by
`p − d mod p`, gives back the original (canonical, consistent) candidates. -/
theorem shift_shift (x : Vals) (oH : Nat) (d : Nat → Nat) (h : HonestAt x oH) (c : Nat) :
    (shift (shift x oH d) oH (fun c => (P - d c % P) % P)).bits oH c = x.bits oH c ∧
      (shift (shift x oH d) oH (fun c => (P - d c % P) % P)).elem oH c = x.elem oH c := by
  obtain ⟨hl, hc, _⟩ := h c
  have hv : (shift (shift x oH d) oH (fun c => (P - d c % P) % P)).val oH c = x.val oH c := by
    rw [shift_val, shift_val]
    have : d c % P < P := Nat.mod_lt _ P_pos
    generalize x.val oH c = v at hc ⊢
    generalize d c = e at this ⊢
    rw [P_eq] at *
    omega
  refine ⟨?_, ?_⟩
  · apply natOf_inj (by simp [shift, hl]) hv
  · apply Fin.ext
    rw [shift_elem_val, shift_elem_val]
    have : d c % P < P := Nat.mod_lt _ P_pos
    have he := fval_lt (x.elem oH c)
    generalize (x.elem oH c).val = v at he ⊢
    generalize d c = e at this ⊢
    rw [P_eq] at *
    omega

/-- **Any target value for a kept reference**: the shifted reference is `ref + d(ref) mod p`, so
`d(ref) = (t − ref) mod p` reaches any canonical `t`. -/
theorem shift_ref (x : Vals) (oH : Nat) (h : HonestAt x oH) (c t : Nat) (ht : t < P) :
    (shift x oH (fun _ => (t + (P - x.val oH c)) % P)).val oH c = t := by
  rw [shift_val]
  have := (h c).2.1
  generalize x.val oH c = v at this ⊢
  rw [P_eq] at *
  omega

/-- The released cut values are unchanged by a shift that is 0 (mod p) on the cut. -/
theorem hiding_cut (x : Vals) (oH : Nat) (d : Nat → Nat) (h : HonestAt x oH) (cut : List Nat)
    (hd : ∀ c ∈ cut, d c % P = 0) : cutRel (shift x oH d) cut = cutRel x cut := by
  unfold cutRel
  congr 1
  funext o
  apply List.map_congr_left
  intro c hcut
  by_cases ho : o = oH
  · subst ho
    obtain ⟨hl, hc, _⟩ := h c
    have hv : (shift x o d).val o c = x.val o c := by
      rw [shift_val, Nat.add_mod, hd c hcut, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hc]
    have hb : (shift x o d).bits o c = x.bits o c := natOf_inj (by simp [shift, hl]) hv
    have he : (shift x o d).elem o c = x.elem o c := by
      apply Fin.ext
      rw [shift_elem_val, Nat.add_mod, hd c hcut, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt (fval_lt _)]
    rw [hb, he]
  · obtain ⟨h1, h2⟩ := shift_other x oH d o c ho
    rw [h1, h2]

/-- The released bucket values are unchanged by a shift whose reference and member shifts cancel
mod p in every bucket pair. -/
theorem hiding_buckets (x : Vals) (oH : Nat) (d : Nat → Nat) (h : HonestAt x oH) (mem : Nat → Nat → Nat)
    (ps : List (Nat × Nat × Nat)) (hd : ∀ e ∈ ps, (d (mem e.2.1 0) + d (mem e.2.1 e.2.2)) % P = 0) :
    bucketRel (shift x oH d) mem ps = bucketRel x mem ps := by
  unfold bucketRel
  apply List.map_congr_left
  intro e he
  by_cases ho : e.1 = oH
  · rw [ho]
    have hr := (h (mem e.2.1 0)).2.1
    have hm := (h (mem e.2.1 e.2.2)).2.1
    have hsr := Nat.mod_lt ((x.val oH (mem e.2.1 0)) + d (mem e.2.1 0)) P_pos
    have hsm := Nat.mod_lt ((x.val oH (mem e.2.1 e.2.2)) + d (mem e.2.1 e.2.2)) P_pos
    have hde := hd e he
    rw [shift_val, shift_val, addModSpec_canonical _ _ hsr hsm, addModSpec_canonical _ _ hr hm]
    congr 1
    · congr 1
      generalize x.val oH (mem e.2.1 0) = a at *
      generalize x.val oH (mem e.2.1 e.2.2) = b at *
      generalize d (mem e.2.1 0) = u at *
      generalize d (mem e.2.1 e.2.2) = v at *
      rw [P_eq] at *
      omega
    · apply Fin.ext
      rw [fadd_val, fadd_val, shift_elem_val, shift_elem_val]
      have h1 := fval_lt (x.elem oH (mem e.2.1 0))
      have h2 := fval_lt (x.elem oH (mem e.2.1 e.2.2))
      generalize (x.elem oH (mem e.2.1 0)).val = a at *
      generalize (x.elem oH (mem e.2.1 e.2.2)).val = b at *
      generalize d (mem e.2.1 0) = u at *
      generalize d (mem e.2.1 e.2.2) = v at *
      rw [P_eq] at *
      omega
  · obtain ⟨h1, h2⟩ := shift_other x oH d e.1 (mem e.2.1 0) ho
    obtain ⟨h3, h4⟩ := shift_other x oH d e.1 (mem e.2.1 e.2.2) ho
    simp only [Vals.val, h1, h2, h3, h4]

/-- **The flags are unchanged by a shift**: the honest party's shifted references stay canonical;
for a bit block the condition "at least 32" must also hold of the shifted reference (a reference
below 32 aborts the honest run itself; probability 32/p). -/
theorem hiding_flag_mask (x : Vals) (oH : Nat) (d : Nat → Nat) (h : HonestAt x oH) (c : Nat) :
    decide ((shift x oH d).val oH c < P) = decide (x.val oH c < P) := by
  rw [shift_val]
  simp [Nat.mod_lt _ P_pos, (h c).2.1]

/-- **P-CUT (c), the core lemma**: for the honest owner `oH` and any shift `d` that is 0 (mod p)
on the cut and cancels in every bucket pair, the values the cut and the buckets release are the
same as without the shift, and the reference flags of word masks too. With `shift_shift` (a
bijection) and `shift_ref` (any target reference), this is plan 7.0's form: the transcript of
the released values is the same for the honest party's kept references and for any other
canonical ones. (The remaining releases do not depend on the honest candidates: the challenges
are independent of them, and an honest party's bit-block checks are 0 for any references at least
32.) -/
theorem hiding_releases (x : Vals) (oH : Nat) (d : Nat → Nat) (h : HonestAt x oH) (cut : List Nat)
    (mem : Nat → Nat → Nat) (ps : List (Nat × Nat × Nat))
    (hcut : ∀ c ∈ cut, d c % P = 0)
    (hbk : ∀ e ∈ ps, (d (mem e.2.1 0) + d (mem e.2.1 e.2.2)) % P = 0) :
    cutRel (shift x oH d) cut = cutRel x cut ∧ bucketRel (shift x oH d) mem ps = bucketRel x mem ps ∧
      ∀ c, decide ((shift x oH d).val oH c < P) = decide (x.val oH c < P) :=
  ⟨hiding_cut x oH d h cut hcut, hiding_buckets x oH d h mem ps hbk, hiding_flag_mask x oH d h⟩

end TlsMpc.Node.Flows.Masks
