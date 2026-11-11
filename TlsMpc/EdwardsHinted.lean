import TlsMpc.EdwardsAffine
import TlsMpc.FieldDagMulti

/-!
Field programs of constant depth for the curve work that used to be long
sequential chains (a square root by a power chain, a table by 256 successive
doublings, a Montgomery ladder, a double-and-add signature check, a
multiplication by the group order). Over a network link every multiplication
level is a round, so depth is what these programs remove.

Three ideas, all on the twisted Edwards form of Curve25519 used by
`TlsMpc/EdwardsAffine.lean`:

* **A square root from an opened masked value** (`liftOpen`, `liftPoint`). For a
  Montgomery `u`, `q = u·(u² + 486662·u + 1)` is `v²` exactly for curve points,
  and the Edwards point is `x = √(−486664)·u/v`, `y = (u − 1)/(u + 1)`. With a
  uniform shared `r` and a uniform shared bit `b` the runtime opens
  `w = q·r²·2^b`. For `q ≠ 0` this is uniform over the nonzero field elements
  whatever `q` is (2 is not a square), so it reveals nothing, not even whether
  `u` is on the curve; `w = 0` exactly when `u = 0` (or `r = 0`). From the
  public `w`: if it is a square, `v = √w / r` is a root of `q` exactly when
  `b = 0`; otherwise `v = √(w/2) / r` is one exactly when `b = 1`. So validity
  is the private bit `sel xor b` for a public `sel`, and no power chain is run.
  An invalid `u` is replaced by the base point inside the program, so that
  everything after it works on a curve point; the private validity travels on.

* **Multiples from hints, checked** (`bases`, `links`, `entries`). To get
  `16^w·P` for a private point `P` without 4·w successive doublings, the
  runtime opens `Z = P + M_A + M_B` for private uniform points `M_A`, `M_B`
  (one from each party, each checked to be on the curve before `Z` is opened;
  `Z` is then uniform). Party A can compute `16^w·(Z − M_A)` and party B
  `16^w·M_B` locally; their difference is `16^w·P`. They enter these as
  private inputs (hints). The program does NOT trust them: window `w` computes
  its own multiples and `16·base_w` from `base_w`, and requires
  `16·base_w = base_(w+1)` (the "links": masked differences that the runtime
  opens and requires to be zero). `entries_sound`: when every link holds, the
  entries are exactly the chain computed from `P` itself, whatever the hints
  were. So a wrong hint can only make a link fail; it cannot change a result.

* **Sums in extended coordinates** (`extAdd`, `extSum`): the complete addition
  without a division, so a balanced sum of n points is 2·log n levels and no
  opening.

Proved here: the step functions and sums evaluate to the stated value
functions (`extAdd_eval`, `window_eval`, `doublings_eval`, `extSum_eval`,
`hinted_eval`, the small programs' `_eval` theorems), the chain soundness
(`entries_sound`, `prepareTable_sound`, `bitTable_sound`) and, through
`FieldDag.compileAll_correct`, that every accepted compilation computes the
program (`compiled_correct`). Not proved (as in `EdwardsAffine`): that
`pointAddValue`/`extAddValue` are the curve's group law, the
Montgomery/Edwards map, or the uniformity statements above. The exports are
checked numerically against independent arithmetic
(`handshake_backend/EmpHybridWork/lower_word_circuits.py`).
-/
namespace TlsMpc.EdwardsHinted
open FieldDag EdwardsAffine

/-! ### Extended coordinates `(X : Y : Z : T)`, `x = X/Z`, `y = Y/Z`, `T = X·Y/Z` -/

structure Ext (α : Type) where
  x : α
  y : α
  z : α
  t : α

abbrev ExtE := Ext Expr
abbrev ExtV := Ext F

def evalExt (input : Nat → F) (p : ExtE) : ExtV :=
  ⟨p.x.eval input, p.y.eval input, p.z.eval input, p.t.eval input⟩

/-- Complete unified addition (`a = −1`), every coordinate scaled by `121666²`
so that the constants stay machine words (`d = −121665/121666`). -/
def extAdd (p q : ExtE) : ExtE :=
  let a := mul (sub p.y p.x) (sub q.y q.x)
  let b := mul (add p.y p.x) (add q.y q.x)
  let c := mul (.const 243330) (mul p.t q.t)
  let d := mul (.const 243332) (mul p.z q.z)
  let e := mul (.const 121666) (sub b a)
  let h := mul (.const 121666) (add b a)
  let f := add d c
  let g := sub d c
  ⟨mul e f, mul g h, mul f g, mul e h⟩

def extAddValue (p q : ExtV) : ExtV :=
  let a := (p.y - p.x) * (q.y - q.x)
  let b := (p.y + p.x) * (q.y + q.x)
  let c := ofNat 243330 * (p.t * q.t)
  let d := ofNat 243332 * (p.z * q.z)
  let e := ofNat 121666 * (b - a)
  let h := ofNat 121666 * (b + a)
  let f := d + c
  let g := d - c
  ⟨e * f, g * h, f * g, e * h⟩

theorem extAdd_eval (input : Nat → F) (p q : ExtE) :
    evalExt input (extAdd p q) = extAddValue (evalExt input p) (evalExt input q) := rfl

def ofAffine (p : Point) : ExtE := ⟨p.1, p.2, .const 1, mul p.1 p.2⟩
def ofAffineValue (p : Value) : ExtV := ⟨p.1, p.2, ofNat 1, p.1 * p.2⟩

def toAffine (p : ExtE) : Point := (div p.x p.z, div p.y p.z)
def toAffineValue (p : ExtV) : Value := (p.x * inverse p.z, p.y * inverse p.z)

theorem ofAffine_eval (input : Nat → F) (p : Point) :
    evalExt input (ofAffine p) = ofAffineValue (evalPoint input p) := rfl
theorem toAffine_eval (input : Nat → F) (p : ExtE) :
    evalPoint input (toAffine p) = toAffineValue (evalExt input p) := rfl

def neutral : ExtE := ⟨.const 0, .const 1, .const 1, .const 0⟩
def neutralValue : ExtV := ⟨ofNat 0, ofNat 1, ofNat 1, ofNat 0⟩

/-- The point if the bit is one, the neutral element if it is zero. -/
def chooseExt (bit : Expr) (p : ExtE) : ExtE :=
  ⟨mul bit p.x, add (.const 1) (mul bit (sub p.y (.const 1))), add (.const 1) (mul bit (sub p.z (.const 1))), mul bit p.t⟩

def chooseExtValue (bit : F) (p : ExtV) : ExtV :=
  ⟨bit * p.x, ofNat 1 + bit * (p.y - ofNat 1), ofNat 1 + bit * (p.z - ofNat 1), bit * p.t⟩

theorem chooseExt_eval (input : Nat → F) (bit : Expr) (p : ExtE) :
    evalExt input (chooseExt bit p) = chooseExtValue (bit.eval input) (evalExt input p) := rfl

/-- The same for an affine point: `Z = 1`, and `T` from the chosen `x`. -/
def chooseAffine (bit : Expr) (p : Point) : ExtE :=
  let x := mul bit p.1
  ⟨x, add (.const 1) (mul bit (sub p.2 (.const 1))), .const 1, mul x p.2⟩

/-- Balanced sum: `2·⌈log₂ n⌉` multiplication levels, no division. -/
def extSum (points : List ExtE) : ExtE :=
  ((reduce extAdd points.length points).head?).getD neutral
def extSumValue (points : List ExtV) : ExtV :=
  ((reduce extAddValue points.length points).head?).getD neutralValue

theorem extSum_eval (input : Nat → F) (points : List ExtE) :
    evalExt input (extSum points) = extSumValue (points.map (evalExt input)) := by
  have h := reduce_map (evalExt input) extAdd extAddValue (extAdd_eval input) points.length points
  unfold extSum extSumValue
  rw [List.length_map, ← h, List.head?_map]
  cases (reduce extAdd points.length points).head? <;> rfl

/-! ### Checks and hints -/

/-- Zero exactly on curve points: `121666·(y² − x² − 1) + 121665·x²·y²`. -/
def curveCheck (p : Point) : Expr :=
  let xx := mul p.1 p.1
  let yy := mul p.2 p.2
  add (mul (.const 121666) (sub (sub yy xx) (.const 1))) (mul (.const 121665) (mul xx yy))

def negate (p : Point) : Point := (sub (.const 0) p.1, p.2)

/-- A base from the two parties' hints at inputs `i … i+3`: A's point minus B's point. -/
def hinted (i : Nat) : Point := pointAdd (inputPoint i) (negate (inputPoint (i + 2)))

theorem hinted_eval (input : Nat → F) (i : Nat) :
    evalPoint input (hinted i) =
      pointAddValue (input i, input (i + 1)) (ofNat 0 - input (i + 2), input (i + 2 + 1)) := rfl

/-- The bases of `count` windows: the first given, the others hinted (four inputs each from `hints`). -/
def bases (first : Point) (hints count : Nat) : List Point :=
  first :: (List.range (count - 1)).map (fun i => hinted (hints + 4 * i))

/-- For consecutive bases `b`, `c`: the coordinates of `next(b) − c`, where `next` is the
second component of the step (what the step itself computes as the following base). -/
def linksFrom (step : Point → List ε × Point) (b : Point) : List Point → List (Expr × Expr)
  | [] => []
  | c :: rest => (sub (step b).2.1 c.1, sub (step b).2.2 c.2) :: linksFrom step c rest

def links (step : Point → List ε × Point) : List Point → List (Expr × Expr)
  | [] => []
  | b :: rest => linksFrom step b rest

/-- Each link coordinate times its own uniform mask (inputs from `masks`): the runtime opens
these and requires zero; a nonzero difference opens as a uniform value. -/
def masked (masks : Nat) (ds : List (Expr × Expr)) : List Expr :=
  ds.zipIdx.flatMap (fun (d, i) => [mul d.1 (.input (masks + 2 * i)), mul d.2 (.input (masks + 2 * i + 1))])

def entries (step : Point → List ε × Point) (bs : List Point) : List ε := bs.flatMap (fun b => (step b).1)

/-- What the entries are when computed from the first base alone: each step's entries, then
the chain from the step's own next base. -/
def chain (stepV : Value → List β × Value) (r : Value) : Nat → List β
  | 0 => []
  | n + 1 => (stepV r).1 ++ chain stepV (stepV r).2 n

/-- Every link holds: each base after the first is what the step computed from the one before. -/
def LinkedFrom (ev : Point → Value) (step : Point → List ε × Point) (b : Point) : List Point → Prop
  | [] => True
  | c :: rest => ev (step b).2 = ev c ∧ LinkedFrom ev step c rest

/-- Soundness of the hints: if every link holds, the entries are the chain from the first
base, whatever the other bases (the hints) are as expressions. -/
theorem entries_sound (ev : Point → Value) (evE : ε → β) (step : Point → List ε × Point)
    (stepV : Value → List β × Value)
    (hstep : ∀ b, (step b).1.map evE = (stepV (ev b)).1 ∧ ev (step b).2 = (stepV (ev b)).2)
    (b : Point) (rest : List Point) (h : LinkedFrom ev step b rest) :
    (entries step (b :: rest)).map evE = chain stepV (ev b) (rest.length + 1) := by
  induction rest generalizing b with
  | nil => simp [entries, chain, (hstep b).1]
  | cons c rest ih =>
    have hc := ih c h.2
    simp only [entries, List.flatMap_cons, List.map_append] at hc ⊢
    rw [hc, (hstep b).1]
    show _ = (stepV (ev b)).1 ++ chain stepV (stepV (ev b)).2 (rest.length + 1)
    rw [← (hstep b).2, h.1]

/-! ### The two steps -/

/-- `EdwardsAffine.window` on values. -/
def windowValue (base : Value) : List Value × Value :=
  let multiples := (List.range (digits - 1)).foldl (fun acc i =>
    let j := i + 2
    acc ++ [pointAddValue (acc.getD ((j + 1) / 2 - 1) base) (acc.getD (j / 2 - 1) base)]) [base]
  let top := multiples.getD (digits - 1) base
  (multiples, pointAddValue top top)

theorem window_eval (input : Nat → F) (b : Point) :
    (window b).1.map (evalPoint input) = (windowValue (evalPoint input b)).1 ∧
      evalPoint input (window b).2 = (windowValue (evalPoint input b)).2 := ⟨rfl, rfl⟩

/-- One window of a bit table: `b, 2b, 4b, 8b` in extended coordinates, and `16b` affine. -/
def doublings (b : Point) : List ExtE × Point :=
  let p1 := ofAffine b
  let p2 := extAdd p1 p1
  let p4 := extAdd p2 p2
  let p8 := extAdd p4 p4
  ([p1, p2, p4, p8], toAffine (extAdd p8 p8))

def doublingsValue (b : Value) : List ExtV × Value :=
  let p1 := ofAffineValue b
  let p2 := extAddValue p1 p1
  let p4 := extAddValue p2 p2
  let p8 := extAddValue p4 p4
  ([p1, p2, p4, p8], toAffineValue (extAddValue p8 p8))

theorem doublings_eval (input : Nat → F) (b : Point) :
    (doublings b).1.map (evalExt input) = (doublingsValue (evalPoint input b)).1 ∧
      evalPoint input (doublings b).2 = (doublingsValue (evalPoint input b)).2 := ⟨rfl, rfl⟩

/-! ### Programs -/

def bitXor (a b : Expr) : Expr := sub (add a b) (mul (.const 2) (mul a b))

def baseX : Nat := 15112221349535400772501151409588531511454012693041857206046113283949847762202
def baseY : Nat := 46316835694926478169428394003475163141307993866256225615783033603165251855960

/-- A square root of `−486664 = −(A + 2)`: the constant of the Montgomery-to-Edwards map. -/
def sqrtMinusA2 : Nat := 6853475219497561581579357271197624642482790079785650197046958215289687604742

theorem sqrtMinusA2_square : (sqrtMinusA2 * sqrtMinusA2 + 486664) % modulus = 0 := by decide

/-- Lifting a Montgomery `u`, first half. Inputs: 0 `u`; 1 a uniform shared mask `r`; 2, 3 the
two parties' private random bits; 4, 5 party A's mask point; 6, 7 party B's.
Outputs: `w = q·r²·(1 + b)` for `b` the XOR of the two bits (opened AFTER the checks);
the two bit checks and the two curve checks (each a function of its owner's inputs only;
opened first, must be zero); `b`. -/
def liftOpen (_ : Unit) : List Expr :=
  let u := Expr.input 0
  let r := Expr.input 1
  let q := mul u (add (add (mul u u) (mul (.const 486662) u)) (.const 1))
  let b := bitXor (.input 2) (.input 3)
  [mul (mul (mul q r) r) (add (.const 1) b), bitCheck (.input 2), bitCheck (.input 3),
    curveCheck (inputPoint 4), curveCheck (inputPoint 6), b]

theorem liftOpen_eval (input : Nat → F) :
    (liftOpen ()).map (Expr.eval input) =
      (let u := input 0
       let b := input 2 + input 3 - ofNat 2 * (input 2 * input 3)
       [u * (u * u + ofNat 486662 * u + ofNat 1) * input 1 * input 1 * (ofNat 1 + b),
        input 2 * (input 2 - ofNat 1), input 3 * (input 3 - ofNat 1),
        ofNat 121666 * (input 5 * input 5 - input 4 * input 4 - ofNat 1) + ofNat 121665 * (input 4 * input 4 * (input 5 * input 5)),
        ofNat 121666 * (input 7 * input 7 - input 6 * input 6 - ofNat 1) + ofNat 121665 * (input 6 * input 6 * (input 7 * input 7)),
        b]) := rfl

/-- Second half. Inputs: 0 the public `√(−486664)/s` for the public root `s` of `w` (or of
`w/2`); 1 the public `sel` (1 when `w` is a square); 2 `u`; 3 `r`; 4 `b`; 5, 6 and 7, 8 the mask
points. Outputs: `valid = sel xor b`; the point `P` (the lifted point when valid, the base
point otherwise); `Z = M_A + M_B + P`, which the runtime opens. The denominator of `y` is
`u + 1` when valid (nonzero: `u = −1` is not on the curve) and 1 otherwise. -/
def liftPoint (_ : Unit) : List Expr :=
  let u := Expr.input 2
  let valid := bitXor (.input 1) (.input 4)
  let x := mul (.input 0) (mul u (.input 3))
  let y := div (sub u (.const 1)) (add (.const 1) (mul valid u))
  let p : Point := (add (.const baseX) (mul valid (sub x (.const baseX))), add (.const baseY) (mul valid (sub y (.const baseY))))
  let z := pointAdd (pointAdd (inputPoint 5) (inputPoint 7)) p
  [valid, p.1, p.2, z.1, z.2]

theorem liftPoint_eval (input : Nat → F) :
    (liftPoint ()).map (Expr.eval input) =
      (let u := input 2
       let valid := input 1 + input 4 - ofNat 2 * (input 1 * input 4)
       let x := input 0 * (u * input 3)
       let y := (u - ofNat 1) * inverse (ofNat 1 + valid * u)
       let p : Value := (ofNat baseX + valid * (x - ofNat baseX), ofNat baseY + valid * (y - ofNat baseY))
       let z := pointAddValue (pointAddValue (input 5, input 6) (input 7, input 8)) p
       [valid, p.1, p.2, z.1, z.2]) := rfl

/-- Input layout of `prepareHinted`: the point (0, 1); 63 hinted bases (4 inputs each) from 2;
126 link masks from 254; the two parties' 252 scalar bits each from 380. -/
def prepareHints : Nat := 2
def prepareMasks : Nat := prepareHints + 4 * (windows - 1)
def prepareBits : Nat := prepareMasks + 2 * (windows - 1)
def prepareInputs : Nat := prepareBits + 2 * scalarBits

def prepareBases (_ : Unit) : List Point := bases (inputPoint 0) prepareHints windows

/-- How many leading outputs of `prepareHinted` the runtime opens and requires to be zero. -/
def prepareHintedChecks : Nat := 2 * scalarBits + 2 * (windows - 1)

/-- `EdwardsAffine.prepare` without its chains: the same table and initial point for a point
already lifted (`liftOpen`, `liftPoint`), with hinted window bases. Outputs: one bit check per
scalar bit, the masked links (all must open to zero), the initial point `(kA + kB)·P`, then
the table (entry `8·w + (j − 1)` is `(j·16^w)·P`, as before). -/
def prepareHinted (_ : Unit) : List Expr :=
  let table := entries window (prepareBases ())
  let bit (i : Nat) : Expr := .input (prepareBits + i)
  let chosen := (List.range (2 * scalarBits)).map (fun i => chooseAffine (bit i) (bitEntry table (i % scalarBits)))
  let initial := toAffine (extSum chosen)
  (List.range (2 * scalarBits)).map (fun i => bitCheck (bit i)) ++ masked prepareMasks (links window (prepareBases ())) ++
    [initial.1, initial.2] ++ table.flatMap (fun p => [p.1, p.2])

/-- When every link of `prepareHinted` holds, its table is the chain of windows computed from
the point at inputs 0, 1 alone: it does not depend on the hints. -/
theorem prepareTable_sound (input : Nat → F)
    (h : LinkedFrom (evalPoint input) window (inputPoint 0) ((List.range (windows - 1)).map (fun i => hinted (prepareHints + 4 * i)))) :
    (entries window (prepareBases ())).map (evalPoint input) = chain windowValue (input 0, input 1) windows := by
  have s := entries_sound (evalPoint input) (evalPoint input) window windowValue (window_eval input) (inputPoint 0) _ h
  have first : evalPoint input (inputPoint 0) = (input 0, input 1) := rfl
  rw [first] at s
  simpa [prepareBases, bases, windows] using s

/-- Per message, as `EdwardsAffine.offsetSum` (same inputs: the initial point, then per window
an entry and its sign) in extended coordinates. Outputs: `Z + Y` and `Z − Y` of the sum, whose
quotient is the Montgomery `u`. -/
def offsetSumFast (_ : Unit) : List Expr :=
  let entry (w : Nat) : ExtE :=
    let x := mul (.input (2 + 3 * w + 2)) (.input (2 + 3 * w))
    ⟨x, .input (2 + 3 * w + 1), .const 1, mul x (.input (2 + 3 * w + 1))⟩
  let sum := extSum (ofAffine (inputPoint 0) :: (List.range windows).map entry)
  [add sum.z sum.y, sub sum.z sum.y]

/-- Input layout of `bitTable`: the point (0, 1); 63 hinted bases from 2; 126 link masks from 254. -/
def bitTableInputs : Nat := 2 + 4 * (windows - 1) + 2 * (windows - 1)

def bitTableBases (_ : Unit) : List Point := bases (inputPoint 0) 2 windows

/-- All `2^i·P`, `i < 256`, in extended coordinates (4 outputs each), after the masked links
(126 outputs that must open to zero). -/
def bitTable (_ : Unit) : List Expr :=
  masked (2 + 4 * (windows - 1)) (links doublings (bitTableBases ())) ++
    (entries doublings (bitTableBases ())).flatMap (fun p => [p.x, p.y, p.z, p.t])

theorem bitTable_sound (input : Nat → F)
    (h : LinkedFrom (evalPoint input) doublings (inputPoint 0) ((List.range (windows - 1)).map (fun i => hinted (2 + 4 * i)))) :
    (entries doublings (bitTableBases ())).map (evalExt input) = chain doublingsValue (input 0, input 1) windows := by
  have s := entries_sound (evalPoint input) (evalExt input) doublings doublingsValue (doublings_eval input) (inputPoint 0) _ h
  have first : evalPoint input (inputPoint 0) = (input 0, input 1) := rfl
  rw [first] at s
  simpa [bitTableBases, bases, windows] using s

def extInput (i : Nat) : ExtE := ⟨.input i, .input (i + 1), .input (i + 2), .input (i + 3)⟩

/-- Bits 3 … 253 of a clamped X25519 scalar are free; bit 254 is set. -/
def agreementBits : Nat := 251

/-- X25519 from a bit table. Inputs: 0 `valid`; 1 a uniform shared mask; then the 252 points
`2^i·P`, `i = 3 … 254` (4 inputs each); then scalar bits 3 … 253. Outputs a numerator and a
denominator whose quotient is the Montgomery `u` of `k·P` when `valid` is one and uniform when
it is zero. -/
def bitSum (_ : Unit) : List Expr :=
  let points := 2
  let bits := points + 4 * (agreementBits + 1)
  let chosen := (List.range agreementBits).map (fun j => chooseExt (.input (bits + j)) (extInput (points + 4 * j)))
  let sum := extSum (chosen ++ [extInput (points + 4 * agreementBits)])
  [add (.input 1) (mul (.input 0) (sub (add sum.z sum.y) (.input 1))), sub sum.z sum.y]

def bitSumInputs : Nat := 2 + 4 * (agreementBits + 1) + agreementBits

/-- The same from affine points (a contact's offset table already holds `2^i·R`): inputs 0
`valid`; 1 a mask; the 252 affine points `2^i·P`, `i = 3 … 254` (2 inputs each) from 2; then
scalar bits 3 … 253. -/
def affineBitSum (_ : Unit) : List Expr :=
  let points := 2
  let bits := points + 2 * (agreementBits + 1)
  let chosen := (List.range agreementBits).map (fun j => chooseAffine (.input (bits + j)) (inputPoint (points + 2 * j)))
  let sum := extSum (chosen ++ [ofAffine (inputPoint (points + 2 * agreementBits))])
  [add (.input 1) (mul (.input 0) (sub (add sum.z sum.y) (.input 1))), sub sum.z sum.y]

def affineBitSumInputs : Nat := 2 + 2 * (agreementBits + 1) + agreementBits

/-- The XEdDSA verification point `[s]B − [h]A` as a sum of chosen table entries.
Inputs: 0 `flip`; the 256 points `2^i·(x, y)` of the key (4 each) from 1; the 256 bits of `h`
from 1025; the 253 points `2^i·B` from 1281; the 253 bits of `s` from 2293. `A = (±x, y)` with
the sign chosen by `flip`, as in `XEdDsaField.signedRun`; outputs the affine coordinates. -/
def signatureSum (_ : Unit) : List Expr :=
  let sign := sub (mul (.const 2) (.input 0)) (.const 1)
  let key (i : Nat) : ExtE :=
    let p := extInput (1 + 4 * i)
    let m := mul (.input (1025 + i)) sign
    ⟨mul m p.x, add (.const 1) (mul (.input (1025 + i)) (sub p.y (.const 1))),
      add (.const 1) (mul (.input (1025 + i)) (sub p.z (.const 1))), mul m p.t⟩
  let chosen := (List.range 256).map key ++
    (List.range 253).map (fun i => chooseExt (.input (2293 + i)) (extInput (1281 + 4 * i)))
  let sum := toAffine (extSum chosen)
  [sum.1, sum.2]

def signatureSumInputs : Nat := 2293 + 253

/-- Torsion check by a hint. Inputs: 0, 1 the point `P`; 2 … 5 the two parties' hints for
`Q = [1/8 mod ℓ]P`; 6 a uniform shared mask. Outputs: `x(8Q) − x(P)` and
`y(8Q) − y(P) + mask·curveCheck(Q)`. Both are zero when `Q` is a curve point with `8Q = P`,
which exists exactly for `P` in the prime-order subgroup; a `Q` off the curve leaves the
second output uniform. -/
def torsionHinted (_ : Unit) : List Expr :=
  let q := hinted 2
  let e := ofAffine q
  let e2 := extAdd e e
  let e4 := extAdd e2 e2
  let e8 := toAffine (extAdd e4 e4)
  [sub e8.1 (.input 0), add (sub e8.2 (.input 1)) (mul (.input 6) (curveCheck q))]

theorem torsionHinted_eval (input : Nat → F) :
    (torsionHinted ()).map (Expr.eval input) =
      (let q := pointAddValue (input 2, input 3) (ofNat 0 - input 4, input 5)
       let e := ofAffineValue q
       let e2 := extAddValue e e
       let e4 := extAddValue e2 e2
       let e8 := toAffineValue (extAddValue e4 e4)
       [e8.1 - input 0,
        e8.2 - input 1 + input 6 * (ofNat 121666 * (q.2 * q.2 - q.1 * q.1 - ofNat 1) + ofNat 121665 * (q.1 * q.1 * (q.2 * q.2)))]) := rfl

/-- Every accepted compilation of any of these programs computes its expressions. -/
theorem compiled_correct (program : List Expr) (artifact : MultiArtifact) (compiled : compileAll program = some artifact)
    (input : Nat → F) :
    artifact.outputs.map (result (concrete input) artifact.nodes) = program.map (Expr.eval input) :=
  compileAll_correct program artifact compiled input

/-- Program named on the command line: input count and output expressions. -/
def find : String → Option (Nat × List Expr)
  | "lift-open" => some (8, liftOpen ())
  | "lift-point" => some (9, liftPoint ())
  | "edwards-prepare-hinted" => some (prepareInputs, prepareHinted ())
  | "edwards-offset-sum-fast" => some (2 + 3 * windows, offsetSumFast ())
  | "edwards-bit-table" => some (bitTableInputs, bitTable ())
  | "edwards-bit-sum" => some (bitSumInputs, bitSum ())
  | "edwards-affine-bit-sum" => some (affineBitSumInputs, affineBitSum ())
  | "edwards-signature-sum" => some (signatureSumInputs, signatureSum ())
  | "edwards-torsion-hinted" => some (7, torsionHinted ())
  | _ => none

#print axioms entries_sound
#print axioms prepareTable_sound
#print axioms bitTable_sound
#print axioms extSum_eval
#print axioms liftPoint_eval

end TlsMpc.EdwardsHinted
