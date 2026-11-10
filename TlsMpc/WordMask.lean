import TlsMpc.BoolDag
import TlsMpc.FieldDag

/-!
Gate-level circuits for full-width conversion masks between the Boolean engine
and the prime field `p = 2^255 - 19`. A word is a list of 255 bit expressions,
least significant first.

The adders use one AND per bit (`carry' = c ⊕ ((a ⊕ c) ∧ (b ⊕ c))`), and constant
operands are folded by the smart constructors, so the gate structure is exactly
what is written here. The theorems relate the value of each circuit, under every
input assignment, to natural-number arithmetic; `BoolDag.compile_correct` carries
them to the exported node list. The cut/bucket protocol that uses these circuits
is not modelled.
-/
namespace TlsMpc.WordMask

open BoolDag

set_option exponentiation.threshold 600

def P : Nat := 57896044618658097711785492504343953926634992332820282019728792003956564819949

theorem P_eq : P = 2 ^ 255 - 19 := by decide
theorem P_eq_modulus : P = FieldDag.modulus := by decide

/-! ### Constant-folding constructors -/

def xor' (a b : Expr) : Expr :=
  match a, b with
  | .const false, b => b
  | a, .const false => a
  | a, b => .bin .xor a b

def and' (a b : Expr) : Expr :=
  match a, b with
  | .const false, _ => .const false
  | _, .const false => .const false
  | .const true, b => b
  | a, .const true => a
  | a, b => .bin .and a b

def not' (a : Expr) : Expr := xor' a (.const true)

@[simp] theorem xor'_eval (env : Nat → Bool) (a b : Expr) :
    (xor' a b).eval env = (a.eval env ^^ b.eval env) := by
  unfold xor'
  split <;> simp [Expr.eval, Bin.eval]

@[simp] theorem and'_eval (env : Nat → Bool) (a b : Expr) :
    (and' a b).eval env = (a.eval env && b.eval env) := by
  unfold and'
  split <;> simp [Expr.eval, Bin.eval]

@[simp] theorem not'_eval (env : Nat → Bool) (a : Expr) : (not' a).eval env = !(a.eval env) := by
  simp [not', Expr.eval]

/-! ### Words and addition -/

/-- Value of a little-endian bit list. -/
def val (env : Nat → Bool) : List Expr → Nat
  | [] => 0
  | b :: bs => (b.eval env).toNat + 2 * val env bs

def sumBit (a b c : Expr) : Expr := xor' (xor' a b) c
/-- Majority with a single AND. -/
def carryBit (a b c : Expr) : Expr := xor' c (and' (xor' a c) (xor' b c))

/-- Ripple addition of equal-length words with carry in; returns sum bits and carry out. -/
def addBits : List Expr → List Expr → Expr → List Expr × Expr
  | a :: as, b :: bs, c =>
      let r := addBits as bs (carryBit a b c)
      (sumBit a b c :: r.1, r.2)
  | _, _, c => ([], c)

/-- The low `n` bits of a constant. -/
def constBits : Nat → Nat → List Expr
  | 0, _ => []
  | n + 1, k => .const (k % 2 == 1) :: constBits n (k / 2)

def inputWord (start : Nat) : List Expr := (List.range 255).map (fun i => .input (start + i))

private theorem full_adder (a b c : Bool) :
    (a ^^ b ^^ c).toNat + 2 * (c ^^ ((a ^^ c) && (b ^^ c))).toNat = a.toNat + b.toNat + c.toNat := by
  cases a <;> cases b <;> cases c <;> rfl

theorem addBits_length (as bs : List Expr) (c : Expr) (h : as.length = bs.length) :
    (addBits as bs c).1.length = as.length := by
  induction as generalizing bs c with
  | nil => cases bs <;> simp [addBits]
  | cons a as ih =>
    cases bs with
    | nil => simp at h
    | cons b bs => simp [addBits, ih bs _ (by simpa using h)]

theorem addBits_val (env : Nat → Bool) (as bs : List Expr) (c : Expr) (h : as.length = bs.length) :
    val env (addBits as bs c).1 + 2 ^ as.length * ((addBits as bs c).2.eval env).toNat =
      val env as + val env bs + (c.eval env).toNat := by
  induction as generalizing bs c with
  | nil =>
    cases bs with
    | nil => simp [addBits, val]
    | cons b bs => simp at h
  | cons a as ih =>
    cases bs with
    | nil => simp at h
    | cons b bs =>
      have hl : as.length = bs.length := by simpa using h
      have ih' := ih bs (carryBit a b c) hl
      have fa := full_adder (a.eval env) (b.eval env) (c.eval env)
      simp only [addBits, val, List.length_cons, sumBit, carryBit, xor'_eval, and'_eval] at ih' ⊢
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ as.length) 2, Nat.mul_assoc]
      omega

theorem val_lt (env : Nat → Bool) (bits : List Expr) : val env bits < 2 ^ bits.length := by
  induction bits with
  | nil => simp [val]
  | cons b bs ih =>
    have hb : (b.eval env).toNat ≤ 1 := Bool.toNat_le _
    simp only [val, List.length_cons, Nat.pow_succ]
    omega

theorem val_append (env : Nat → Bool) (xs ys : List Expr) :
    val env (xs ++ ys) = val env xs + 2 ^ xs.length * val env ys := by
  induction xs with
  | nil => simp [val]
  | cons x xs ih =>
    simp only [List.cons_append, val, ih, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_comm (2 ^ xs.length) 2, Nat.mul_assoc]
    omega

theorem constBits_length (n k : Nat) : (constBits n k).length = n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => simp [constBits, ih]

theorem constBits_val (env : Nat → Bool) (n k : Nat) : val env (constBits n k) = k % 2 ^ n := by
  induction n generalizing k with
  | zero => simp [constBits, val, Nat.mod_one]
  | succ n ih =>
    simp only [constBits, val, ih, Expr.eval]
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ n) 2, Nat.mod_mul]
    have : (k % 2 == 1).toNat = k % 2 := by
      rcases Nat.mod_two_eq_zero_or_one k with h | h <;> simp [h]
    omega

theorem inputWord_length (start : Nat) : (inputWord start).length = 255 := by simp [inputWord]

/-! ### The two primitives -/

/-- One bit: the carry out of `x + (2^n - c)`, i.e. `x ≥ c`, for an `n`-bit word. -/
def atLeast (c : Nat) (x : List Expr) : Expr :=
  (addBits x (constBits x.length (2 ^ x.length - c)) (.const false)).2

theorem atLeast_eval (env : Nat → Bool) (c : Nat) (x : List Expr) (hc0 : 0 < c) (hc : c ≤ 2 ^ x.length) :
    (atLeast c x).eval env = decide (c ≤ val env x) := by
  have h := addBits_val env x (constBits x.length (2 ^ x.length - c)) (.const false)
    (by rw [constBits_length])
  have hlen := addBits_length x (constBits x.length (2 ^ x.length - c)) (.const false)
    (by rw [constBits_length])
  have hsum := val_lt env (addBits x (constBits x.length (2 ^ x.length - c)) (.const false)).1
  have hx := val_lt env x
  rw [hlen] at hsum
  rw [constBits_val, Nat.mod_eq_of_lt (by omega)] at h
  simp only [Expr.eval, Bool.toNat_false, Nat.add_zero] at h
  unfold atLeast
  generalize (addBits x (constBits x.length (2 ^ x.length - c)) (.const false)).2.eval env = carry at h
  generalize val env (addBits x (constBits x.length (2 ^ x.length - c)) (.const false)).1 = low at h hsum
  generalize 2 ^ x.length = m at *
  cases carry
  · simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at h
    simp only [Bool.false_eq, decide_eq_false_iff_not]
    omega
  · simp only [Bool.toNat_true, Nat.mul_one] at h
    simp only [Bool.true_eq, decide_eq_true_eq]
    omega

def mux (sel : Expr) (yes no : List Expr) : List Expr :=
  List.zipWith (fun y n => xor' n (and' sel (xor' n y))) yes no

theorem mux_val (env : Nat → Bool) (sel : Expr) (yes no : List Expr) (h : yes.length = no.length) :
    val env (mux sel yes no) = if sel.eval env then val env yes else val env no := by
  induction yes generalizing no with
  | nil =>
    cases no with
    | nil => simp [mux, val]
    | cons n ns => simp at h
  | cons y ys ih =>
    cases no with
    | nil => simp at h
    | cons n ns =>
      have ih' := ih ns (by simpa using h)
      simp only [mux, List.zipWith_cons_cons, val, xor'_eval, and'_eval] at ih' ⊢
      rw [ih']
      cases sel.eval env <;> cases n.eval env <;> cases y.eval env <;> simp

/-- `s mod p` for a 256-bit `s < 2p`: subtract `p` exactly when `s ≥ p`. Output is 255 bits. -/
def condSub (s : List Expr) : List Expr :=
  let r := addBits s (constBits 256 (2 ^ 256 - P)) (.const false)
  mux r.2 (r.1.take 255) (s.take 255)

theorem val_take (env : Nat → Bool) (bits : List Expr) (n : Nat) :
    val env (bits.take n) = val env bits % 2 ^ n := by
  induction bits generalizing n with
  | nil => simp [val]
  | cons b bs ih =>
    cases n with
    | zero => simp [val, Nat.mod_one]
    | succ n =>
      have hb : (b.eval env).toNat ≤ 1 := Bool.toNat_le _
      have h1 : ((b.eval env).toNat + 2 * val env bs) % 2 = (b.eval env).toNat := by omega
      have h2 : ((b.eval env).toNat + 2 * val env bs) / 2 = val env bs := by omega
      simp only [List.take_succ_cons, val, ih, Nat.pow_succ]
      rw [Nat.mul_comm (2 ^ n) 2, Nat.mod_mul, h1, h2]

theorem condSub_val (env : Nat → Bool) (s : List Expr) (hlen : s.length = 256) (hs : val env s < 2 * P) :
    val env (condSub s) = val env s % P := by
  have hP : P = 57896044618658097711785492504343953926634992332820282019728792003956564819949 := rfl
  have hc : (constBits 256 (2 ^ 256 - P)).length = s.length := by rw [constBits_length, hlen]
  have h := addBits_val env s (constBits 256 (2 ^ 256 - P)) (.const false) hc.symm
  have hl := addBits_length s (constBits 256 (2 ^ 256 - P)) (.const false) hc.symm
  have hlow := val_lt env (addBits s (constBits 256 (2 ^ 256 - P)) (.const false)).1
  rw [hl, hlen] at hlow
  rw [constBits_val, hlen] at h
  simp only [Expr.eval, Bool.toNat_false, Nat.add_zero] at h
  unfold condSub
  rw [mux_val env _ _ _ (by simp [hl, hlen]), val_take, val_take]
  generalize (addBits s (constBits 256 (2 ^ 256 - P)) (.const false)).2.eval env = carry at h
  generalize val env (addBits s (constBits 256 (2 ^ 256 - P)) (.const false)).1 = low at h hlow
  rw [hP] at h hs ⊢
  cases carry
  · simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at h
    simp only [Bool.false_eq_true, if_false]
    omega
  · simp only [Bool.toNat_true, Nat.mul_one] at h
    simp only [if_true]
    omega

/-! ### Word operations -/

/-- `(x + y) mod p` for canonical 255-bit `x`, `y`. 765 AND gates. -/
def modAdd (x y : List Expr) : List Expr :=
  let r := addBits x y (.const false)
  condSub (r.1 ++ [r.2])

/-- `u mod p` for any 255-bit `u`. -/
def reduceOnce (u : List Expr) : List Expr := condSub (u ++ [.const false])

def belowP (x : List Expr) : Expr := not' (atLeast P x)
def atLeast32 (x : List Expr) : Expr := atLeast 32 x
def isZero (x : List Expr) : Expr := not' (atLeast 1 x)
def xorWord (x y : List Expr) : List Expr := List.zipWith xor' x y

theorem modAdd_val (env : Nat → Bool) (x y : List Expr) (hx : x.length = 255) (hy : y.length = 255)
    (vx : val env x < P) (vy : val env y < P) :
    val env (modAdd x y) = (val env x + val env y) % P := by
  have h := addBits_val env x y (.const false) (by rw [hx, hy])
  have hl := addBits_length x y (.const false) (by rw [hx, hy])
  simp only [Expr.eval, Bool.toNat_false, Nat.add_zero] at h
  have hv : val env ((addBits x y (.const false)).1 ++ [(addBits x y (.const false)).2]) =
      val env x + val env y := by
    rw [val_append, hl]
    simp only [val, Nat.mul_zero, Nat.add_zero]
    rw [← h]
  unfold modAdd
  rw [condSub_val env _ (by simp [hl, hx]) (by rw [hv]; omega), hv]

theorem reduceOnce_val (env : Nat → Bool) (u : List Expr) (hu : u.length = 255) :
    val env (reduceOnce u) = val env u % P := by
  have hP : P = 57896044618658097711785492504343953926634992332820282019728792003956564819949 := rfl
  have hlt := val_lt env u
  rw [hu] at hlt
  have hv : val env (u ++ [Expr.const false]) = val env u := by
    rw [val_append]; simp [val, Expr.eval]
  unfold reduceOnce
  rw [condSub_val env _ (by simp [hu]) (by rw [hv, hP]; omega), hv]

theorem belowP_eval (env : Nat → Bool) (x : List Expr) (hx : x.length = 255) :
    (belowP x).eval env = decide (val env x < P) := by
  have hP : P = 57896044618658097711785492504343953926634992332820282019728792003956564819949 := rfl
  rw [belowP, not'_eval, atLeast_eval env P x (by rw [hP]; omega) (by rw [hx, hP]; omega)]
  by_cases h : P ≤ val env x <;> simp [h] <;> omega

theorem atLeast32_eval (env : Nat → Bool) (x : List Expr) (hx : x.length = 255) :
    (atLeast32 x).eval env = decide (32 ≤ val env x) :=
  atLeast_eval env 32 x (by omega) (by rw [hx]; omega)

theorem isZero_eval (env : Nat → Bool) (x : List Expr) (hx : x.length = 255) :
    (isZero x).eval env = decide (val env x = 0) := by
  rw [isZero, not'_eval, atLeast_eval env 1 x (by omega) (by rw [hx]; omega)]
  by_cases h : 1 ≤ val env x <;> simp [h] <;> omega

theorem modAdd_length (x y : List Expr) (hx : x.length = 255) (hy : y.length = 255) :
    (modAdd x y).length = 255 := by
  have hl := addBits_length x y (.const false) (by rw [hx, hy])
  have hl2 := addBits_length ((addBits x y (.const false)).1 ++ [(addBits x y (.const false)).2])
    (constBits 256 (2 ^ 256 - P)) (.const false) (by simp [hl, hx, constBits_length])
  simp [modAdd, condSub, mux, hl, hl2, hx]

theorem reduceOnce_length (u : List Expr) (hu : u.length = 255) : (reduceOnce u).length = 255 := by
  have hl := addBits_length (u ++ [Expr.const false]) (constBits 256 (2 ^ 256 - P)) (.const false)
    (by simp [hu, constBits_length])
  simp [reduceOnce, condSub, mux, hl, hu]

/-! ### Exported circuits. Inputs: word `x` at 0..254, word `y` at 255..509. -/

def X : List Expr := inputWord 0
def Y : List Expr := inputWord 255

/-- 255 outputs: `(x + y) mod p`. Bucket checks, and adding a public constant. -/
def modAddCircuit : List Expr := modAdd X Y

/-- 255 outputs `(rA + rB) mod p`, then one flag: both references canonical. -/
def finalizeMaskCircuit : List Expr := modAdd X Y ++ [and' (belowP X) (belowP Y)]

/-- 255 outputs `rA xor rB`, then one flag: both canonical and both at least 32. -/
def finalizeBitsCircuit : List Expr :=
  xorWord X Y ++ [and' (and' (belowP X) (belowP Y)) (and' (atLeast32 X) (atLeast32 Y))]

/-- 255 outputs: `((u mod p) + r) mod p` for any 255-bit `u` and canonical `r`. -/
def intoFieldCircuit : List Expr := modAdd (reduceOnce X) Y

/-- One output: the XOR of inputs 0 and 1. Used in parallel copies for share and mask XORs. -/
def xorBitCircuit : List Expr := [xor' (.input 0) (.input 1)]

/-- AND of the complements: true exactly when every bit is false. -/
def allZero : List Expr → Expr
  | [] => .const true
  | b :: bs => and' (not' b) (allZero bs)

theorem allZero_eval (env : Nat → Bool) (bits : List Expr) :
    (allZero bits).eval env = bits.all (fun b => !(b.eval env)) := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp [allZero, ih]

/-- One output: the first `n` inputs equal the next `n` inputs, bit for bit. -/
def equalCircuit (n : Nat) : List Expr :=
  [allZero ((List.range n).map (fun i => xor' (.input i) (.input (n + i))))]

theorem equalCircuit_eval (env : Nat → Bool) (n : Nat) :
    (equalCircuit n).map (Expr.eval env) = [decide (∀ i, i < n → env i = env (n + i))] := by
  simp only [equalCircuit, List.map_cons, List.map_nil, allZero_eval, List.all_map]
  congr 1
  rw [Bool.eq_iff_iff]
  simp [List.all_eq_true, Expr.eval]

/-- Two outputs: `value = expected`, then `value ≠ 0`. -/
def statusCircuit : List Expr := [isZero (xorWord X Y), not' (isZero X)]

theorem intoField_val (env : Nat → Bool) (vy : val env Y < P) :
    val env intoFieldCircuit = (val env X % P + val env Y) % P := by
  have hP : 0 < P := by decide
  have hX : X.length = 255 := inputWord_length 0
  have hY : Y.length = 255 := inputWord_length 255
  unfold intoFieldCircuit
  rw [modAdd_val env (reduceOnce X) Y (reduceOnce_length X hX) hY
      (by rw [reduceOnce_val env X hX]; exact Nat.mod_lt _ hP) vy,
    reduceOnce_val env X hX]

theorem modAddCircuit_val (env : Nat → Bool) (vx : val env X < P) (vy : val env Y < P) :
    val env modAddCircuit = (val env X + val env Y) % P :=
  modAdd_val env X Y (inputWord_length 0) (inputWord_length 255) vx vy

/-- Masking then unmasking in the field recovers the value: the two conversion identities. -/
theorem into_field_roundtrip (u r : Nat) (hr : r < P) : ((u % P + r) % P + (P - r)) % P = u % P := by
  have hP : 0 < P := by decide
  have h1 : (u % P + r) % P = if u % P + r < P then u % P + r else u % P + r - P := by
    have := Nat.mod_lt u hP
    split
    · exact Nat.mod_eq_of_lt (by omega)
    · rw [Nat.mod_eq_sub_mod (by omega)]; exact Nat.mod_eq_of_lt (by omega)
  have := Nat.mod_lt u hP
  rw [h1]
  split
  · rw [show u % P + r + (P - r) = u % P + P by omega, Nat.add_mod_right, Nat.mod_mod]
  · rw [show u % P + r - P + (P - r) = u % P by omega, Nat.mod_mod]

theorem from_field_roundtrip (x r : Nat) (hx : x < P) (hr : r < P) :
    (r + (x + (P - r)) % P) % P = x := by
  have hP : 0 < P := by decide
  rw [Nat.add_mod_mod, show r + (x + (P - r)) = x + P by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hx]

#print axioms modAdd_val
#print axioms reduceOnce_val
#print axioms belowP_eval
#print axioms atLeast32_eval
#print axioms isZero_eval
#print axioms intoField_val
#print axioms modAddCircuit_val
#print axioms into_field_roundtrip
#print axioms from_field_roundtrip

end TlsMpc.WordMask
