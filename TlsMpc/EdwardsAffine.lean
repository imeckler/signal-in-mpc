import TlsMpc.FieldDag

/-!
Field programs for the offset sealed-sender agreement
(`TlsMpc/OffsetAgreement.lean`, `SEALED_SENDER_AGREEMENT.md` variant C), as
affine arithmetic on the twisted Edwards form of Curve25519,
`-x² + y² = 1 + d·x²·y²` with `d = -121665/121666`.

Whole computations are single programs: the recipient point with its checks,
the table of multiples together with the initial point, and the per-message
sum. Divisions are the field-program `div`; the complete addition law has
nonzero denominators for curve points, so a zero denominator (on which the
runtime aborts) cannot arise from valid inputs.

Proved here: the programs evaluate to the stated point functions
(`pointAdd_eval`, `choose_eval`, `addAll_eval`, `offsetSum_eval`). Not proved:
that `pointAddValue` is the curve's group law, or the Montgomery/Edwards maps.
The exports are checked numerically against an independent implementation.
-/
namespace TlsMpc.EdwardsAffine
open FieldDag

def mul (a b : Expr) : Expr := .bin .mul a b
def add (a b : Expr) : Expr := .bin .add a b
def sub (a b : Expr) : Expr := .bin .sub a b
def div (a b : Expr) : Expr := .bin .div a b

abbrev Point := Expr × Expr
abbrev Value := F × F

/-- Complete twisted Edwards addition, scaled by 121666 to keep constants small. -/
def pointAdd (p q : Point) : Point :=
  let xx := mul p.1 q.1
  let yy := mul p.2 q.2
  let t := mul (.const 121665) (mul xx yy)
  (div (mul (.const 121666) (add (mul p.1 q.2) (mul p.2 q.1))) (sub (.const 121666) t),
   div (mul (.const 121666) (add yy xx)) (add (.const 121666) t))

def pointAddValue (p q : Value) : Value :=
  let t := ofNat 121665 * (p.1 * q.1 * (p.2 * q.2))
  (ofNat 121666 * (p.1 * q.2 + p.2 * q.1) * inverse (ofNat 121666 - t),
   ofNat 121666 * (p.2 * q.2 + p.1 * q.1) * inverse (ofNat 121666 + t))

def evalPoint (input : Nat → F) (p : Point) : Value := (p.1.eval input, p.2.eval input)

theorem pointAdd_eval (input : Nat → F) (p q : Point) :
    evalPoint input (pointAdd p q) = pointAddValue (evalPoint input p) (evalPoint input q) := rfl

/-- The point if the bit is one, the neutral element `(0, 1)` if it is zero. -/
def choose (bit : Expr) (p : Point) : Point :=
  (mul bit p.1, add (.const 1) (mul bit (sub p.2 (.const 1))))

def chooseValue (bit : F) (p : Value) : Value := (bit * p.1, ofNat 1 + bit * (p.2 - ofNat 1))

theorem choose_eval (input : Nat → F) (bit : Expr) (p : Point) :
    evalPoint input (choose bit p) = chooseValue (bit.eval input) (evalPoint input p) := rfl

def addAll (start : Point) (points : List Point) : Point := points.foldl pointAdd start
def addAllValue (start : Value) (points : List Value) : Value := points.foldl pointAddValue start

theorem addAll_eval (input : Nat → F) (start : Point) (points : List Point) :
    evalPoint input (addAll start points) =
      addAllValue (evalPoint input start) (points.map (evalPoint input)) := by
  induction points generalizing start with
  | nil => rfl
  | cons p rest ih => simp only [addAll, addAllValue, List.foldl_cons, List.map_cons] at ih ⊢; rw [ih, pointAdd_eval]

/-! Balanced sums: the same number of additions as a chain, but logarithmic
depth, so the runtime needs few rounds. -/

def pairUp (f : α → α → α) : List α → List α
  | a :: b :: rest => f a b :: pairUp f rest
  | rest => rest

def reduce (f : α → α → α) : Nat → List α → List α
  | 0, l => l
  | n + 1, l => reduce f n (pairUp f l)

theorem pairUp_map (g : α → β) (f : α → α → α) (f' : β → β → β)
    (h : ∀ a b, g (f a b) = f' (g a) (g b)) : ∀ l : List α, (pairUp f l).map g = pairUp f' (l.map g)
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by simp [pairUp, h, pairUp_map g f f' h rest]

theorem reduce_map (g : α → β) (f : α → α → α) (f' : β → β → β)
    (h : ∀ a b, g (f a b) = f' (g a) (g b)) (n : Nat) (l : List α) :
    (reduce f n l).map g = reduce f' n (l.map g) := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih => simp [reduce, ih, pairUp_map g f f' h]

def sumTree (points : List Point) : Point :=
  ((reduce pointAdd points.length points).head?).getD (.const 0, .const 1)
def sumTreeValue (points : List Value) : Value :=
  ((reduce pointAddValue points.length points).head?).getD (ofNat 0, ofNat 1)

theorem sumTree_eval (input : Nat → F) (points : List Point) :
    evalPoint input (sumTree points) = sumTreeValue (points.map (evalPoint input)) := by
  have h := reduce_map (evalPoint input) pointAdd pointAddValue (pointAdd_eval input) points.length points
  unfold sumTree sumTreeValue
  rw [List.length_map, ← h, List.head?_map]
  cases (reduce pointAdd points.length points).head? <;> rfl

def inputPoint (index : Nat) : Point := (.input index, .input (index + 1))

/-! ### Programs -/

def windows : Nat := 63
def digits : Nat := 15
def scalarBits : Nat := 252

/-- A square root of −1: `2^((p−1)/4)`. -/
def sqrtMinusOne : Nat := 19681161376707505956807079304988542015446066515923890162744021073123829784752

theorem sqrtMinusOne_square : (sqrtMinusOne * sqrtMinusOne + 1) % modulus = 0 := by decide

/-- A point with Montgomery coordinate `u`, and a value that is zero exactly
when the derivation is valid (`u` is on the curve, not its twist).

`y = (u − 1)/(u + 1)`, `x² = 121666·(y² − 1)/(121666 − 121665·y²)`,
`c = (x²)^((p+3)/8)`; then `c² = ±x²` when `x²` is a square, and
`x = c` or `c·√−1` accordingly, chosen by `b = (c² + x²)/(2·x²)`.
The check value is `c⁴ − x⁴`. Which of the two roots comes out does not
matter: the agreement only uses `u`-coordinates. -/
def recipient (u : Expr) : Point × Expr :=
  let y := div (sub u (.const 1)) (add u (.const 1))
  let yy := mul y y
  let xx := div (mul (.const 121666) (sub yy (.const 1))) (sub (.const 121666) (mul (.const 121665) yy))
  let t := (List.range 250).foldl (fun t _ => mul (mul t t) xx) xx     -- xx^(2^251 − 1)
  let c := mul t t                                                      -- xx^(2^252 − 2)
  let cc := mul c c
  let b := div (add cc xx) (mul (.const 2) xx)
  let x := mul c (add (.const sqrtMinusOne) (mul b (.const (modulus + 1 - sqrtMinusOne))))
  ((x, y), mul (sub cc xx) (add cc xx))

/-- Zero exactly on bits. -/
def bitCheck (b : Expr) : Expr := mul b (sub b (.const 1))

/-- One window: `base, 2·base, …, 15·base` and `16·base`, each multiple the
sum of its two halves (`j = ⌈j/2⌉ + ⌊j/2⌋`), so four additions deep. -/
def window (base : Point) : List Point × Point :=
  let multiples := (List.range digits).foldl (fun acc i =>
    let j := i + 2
    acc ++ [pointAdd (acc.getD ((j + 1) / 2 - 1) base) (acc.getD (j / 2 - 1) base)]) [base]
  (multiples.take digits, multiples.getD digits base)

/-- All windows: entry `15·w + (j − 1)` is `(j·16^w)·R`. -/
def table (base : Point) : List Point :=
  ((List.range windows).foldl (fun state _ =>
    let next := window state.2
    (state.1 ++ next.1, next.2)) (([] : List Point), base)).1

/-- The table entry for bit `i` of a scalar: `2^i·R`. -/
def bitEntry (entries : List Point) (i : Nat) : Point :=
  entries.getD (digits * (i / 4) + (2 ^ (i % 4) - 1)) (.const 0, .const 1)

/-- How many leading outputs of `prepare` the runtime opens and requires to be zero. -/
def prepareChecks : Nat := 1 + 2 * scalarBits

/-- Per conversation. Inputs: the recipient's `u` (0), a uniform shared mask
nobody knows (1), then the two parties' private scalar bits (252 each).
Outputs: `prepareChecks` values that must open to zero (the masked curve
check, so a failing check reveals nothing else; and one bit check per scalar
bit, each a function of its owner's input only), then the initial point
`(kA + kB)·R` (2 values), then the table (2 values per entry). -/
def prepare : List Expr :=
  let (point, valid) := recipient (.input 0)
  let entries := table point
  let bits := (List.range (2 * scalarBits)).map (fun i => Expr.input (2 + i))
  let chosen := (List.range (2 * scalarBits)).map (fun i => choose (.input (2 + i)) (bitEntry entries (i % scalarBits)))
  let initial := sumTree chosen
  [mul valid (.input 1)] ++ bits.map bitCheck ++ [initial.1, initial.2] ++ entries.flatMap (fun p => [p.1, p.2])

/-- Per message. Inputs: the initial point (0, 1), then one table entry (or the
neutral element) per window. Output: the Montgomery `u = (1 + y)/(1 − y)` of
their sum. -/
def offsetSum : List Expr :=
  let sum := sumTree (inputPoint 0 :: (List.range windows).map (fun w => inputPoint (2 + 2 * w)))
  [div (add (.const 1) sum.2) (sub (.const 1) sum.2)]

theorem offsetSum_eval (input : Nat → F) :
    offsetSum.map (Expr.eval input) =
      (let sum := sumTreeValue ((input 0, input 1) :: (List.range windows).map (fun w => (input (2 + 2 * w), input (2 + 2 * w + 1))))
       [(ofNat 1 + sum.2) * inverse (ofNat 1 - sum.2)]) := by
  have h := sumTree_eval input (inputPoint 0 :: (List.range windows).map (fun w => inputPoint (2 + 2 * w)))
  simp only [List.map_cons, List.map_map] at h
  show [((add (.const 1) (sumTree _).2).eval input) * inverse ((sub (.const 1) (sumTree _).2).eval input)] = _
  have second := congrArg Prod.snd h
  simp only [evalPoint] at second
  simp only [add, sub, Expr.eval, Bin.eval, second]
  rfl

#print axioms sumTree_eval
#print axioms offsetSum_eval

end TlsMpc.EdwardsAffine
