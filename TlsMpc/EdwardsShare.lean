import TlsMpc.FieldDag

/-!
Field programs for a Diffie–Hellman agreement with a PUBLIC peer point and an
additively shared scalar `k = kA + kB`.

Each party computes its own multiple `T = k_party · S` of the public peer point
locally, as a point `(x, y)` on the twisted Edwards form of Curve25519
(`-x² + y² = 1 + d·x²·y²`, `d = -121665/121666`), and gives its coordinates to
the field engine as private inputs. The engines then compute only

* `onCurve`: a value that is zero exactly when a party's input satisfies the
  curve equation (opened, so an off-curve input aborts), and
* `addU`: the Montgomery `u`-coordinate of `T_A + T_B` in projective form.

To keep every constant small the equations are scaled by `121666`:
`d·121666 = -121665`, so with `A = x₁x₂`, `B = y₁y₂`

  `den = 121666 + 121665·A·B`      (`121666 · (1 - d·A·B)`)
  `num = 121666 · (A + B)`         (`121666 · (y₁y₂ + x₁x₂)`)

and the sum has `y₃ = num / den`, hence `u₃ = (1 + y₃)/(1 - y₃) =
(den + num)/(den - num)`. The program returns `[den + num, den - num]`; the
caller divides through a masked inversion.

What is proved here: the compiled programs evaluate to exactly these
polynomial expressions (`FieldDag.compile_correct` applies to them like to any
other expression). What is NOT mechanised: that these polynomials are the
Edwards addition law, that the law is complete on this curve, the birational
map to the Montgomery form, and therefore that the result equals RFC 7748
X25519 of the summed scalar. Those are classical facts used as assumptions;
the export is checked numerically against an independent ladder.
-/
namespace TlsMpc.EdwardsShare
open FieldDag

def mul (a b : Expr) : Expr := .bin .mul a b
def add (a b : Expr) : Expr := .bin .add a b
def sub (a b : Expr) : Expr := .bin .sub a b

/-- `121666·(y² - x² - 1) + 121665·x²·y²`. Inputs: `x` (0), `y` (1). -/
def onCurve : Expr :=
  let xx := mul (.input 0) (.input 0)
  let yy := mul (.input 1) (.input 1)
  add (mul (.const 121666) (sub (sub yy xx) (.const 1))) (mul (.const 121665) (mul xx yy))

/-- `[den + num, den - num]`. Inputs: `x₁` (0), `y₁` (1), `x₂` (2), `y₂` (3). -/
def addU : List Expr :=
  let a := mul (.input 0) (.input 2)
  let b := mul (.input 1) (.input 3)
  let den := add (.const 121666) (mul (.const 121665) (mul a b))
  let num := mul (.const 121666) (add a b)
  [add den num, sub den num]

theorem onCurve_eval (input : Nat → F) :
    onCurve.eval input =
      ofNat 121666 * (input 1 * input 1 - input 0 * input 0 - ofNat 1) +
        ofNat 121665 * (input 0 * input 0 * (input 1 * input 1)) := rfl

theorem addU_eval (input : Nat → F) :
    addU.map (Expr.eval input) =
      [ofNat 121666 + ofNat 121665 * (input 0 * input 2 * (input 1 * input 3)) +
          ofNat 121666 * (input 0 * input 2 + input 1 * input 3),
        ofNat 121666 + ofNat 121665 * (input 0 * input 2 * (input 1 * input 3)) -
          ofNat 121666 * (input 0 * input 2 + input 1 * input 3)] := rfl

#print axioms onCurve_eval
#print axioms addU_eval

end TlsMpc.EdwardsShare
