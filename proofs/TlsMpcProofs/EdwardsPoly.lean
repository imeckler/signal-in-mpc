import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Polynomial identities behind the twisted Edwards group law (a = −1)

Curve: `−x² + y² = 1 + d·x²·y²`. Sum of `(x₁, y₁)` and `(x₂, y₂)`:
`((x₁y₂ + y₁x₂)/(1 + d·x₁x₂y₁y₂), (y₁y₂ + x₁x₂)/(1 − d·x₁x₂y₁y₂))`.

Each theorem is an identity between polynomials in the coordinates and `d` that holds modulo the
curve equations of the points involved, proved by `linear_combination` with explicit cofactors
(route (a) of the plan: Hales–Raya, "Formal proof of the group law for Edwards curves", where the
identity is shown to lie in the ideal of the curve equations). The cofactors were found by
rewriting `d·xᵢ²·yᵢ² → yᵢ² − xᵢ² − 1` until nothing was left (no power of `d` had to be multiplied
in), with a small script (`.deps/lowering-scratch/hg_gen.py`, not part of the proof: Lean's `ring`
checks every cofactor here). They hold in any commutative ring; no hypothesis on `d`.

`mont_double_poly` and `mont_diffadd_poly` are the Montgomery x-only doubling and differential
addition, written in Edwards coordinates through `u = (1 + y)/(1 − y)` (used by
`MontgomeryLadder.lean`).

This file is generated; do not edit by hand.
-/

namespace TlsMpcProofs.Edwards

variable {R : Type*} [CommRing R]

/-- Closure: the sum of two curve points satisfies the curve equation, denominators cleared. -/
theorem closure_poly (d x1 y1 x2 y2 : R) (h1 : -x1^2 + y1^2 = 1 + d*x1^2*y1^2) (h2 : -x2^2 + y2^2 = 1 + d*x2^2*y2^2) :
    -(x1*y2 + y1*x2)^2*(1 - d*x1*x2*y1*y2)^2 + (y1*y2 + x1*x2)^2*(1 + d*x1*x2*y1*y2)^2 =
      (1 + d*x1*x2*y1*y2)^2*(1 - d*x1*x2*y1*y2)^2 + d*(x1*y2 + y1*x2)^2*(y1*y2 + x1*x2)^2 := by
  linear_combination
    (d^3 * x1^2 * y1^2 * x2^4 * y2^4 - d^2 * x1^2 * x2^4 * y2^4 + d^2 * y1^2 * x2^4 * y2^4
      - d^2 * x2^4 * y2^4 - d * x1^2 * x2^4 * y2^2 + d * x1^2 * x2^2 * y2^4 + d * y1^2 * x2^4 * y2^2
      - d * y1^2 * x2^2 * y2^4 - 2 * d * x2^4 * y2^4 - 2 * d * x2^2 * y2^2 - 2 * x2^4 * y2^2 + x2^4
      + 2 * x2^2 * y2^4 - 4 * x2^2 * y2^2 + y2^4) * h1 +
    (d * x1^4 * x2^2 * y2^2 + 2 * d * x1^2 * x2^2 * y2^2 + d * y1^4 * x2^2 * y2^2
      - 2 * d * y1^2 * x2^2 * y2^2 + d * x2^2 * y2^2 + 2 * x1^2 * x2^2 * y2^2 - x1^2 * x2^2
      + x1^2 * y2^2 - 2 * y1^2 * x2^2 * y2^2 + y1^2 * x2^2 - y1^2 * y2^2 + 2 * x2^2 * y2^2 - x2^2
      + y2^2 + 1) * h2

/-- Associativity, x-coordinate: numerator of `(P₁+P₂)+P₃` times denominator of `P₁+(P₂+P₃)` equals the converse, modulo the three curve equations. -/
theorem assoc_x_poly (d x1 y1 x2 y2 x3 y3 : R) (h1 : -x1^2 + y1^2 = 1 + d*x1^2*y1^2) (h2 : -x2^2 + y2^2 = 1 + d*x2^2*y2^2) (h3 : -x3^2 + y3^2 = 1 + d*x3^2*y3^2) :
    ((x1*y2 + y1*x2)*(1 - d*x1*x2*y1*y2)*y3 + (y1*y2 + x1*x2)*(1 + d*x1*x2*y1*y2)*x3) * ((1 + d*x2*x3*y2*y3)*(1 - d*x2*x3*y2*y3) + d*x1*y1*(x2*y3 + y2*x3)*(y2*y3 + x2*x3)) =
      (x1*(y2*y3 + x2*x3)*(1 + d*x2*x3*y2*y3) + y1*(x2*y3 + y2*x3)*(1 - d*x2*x3*y2*y3)) * ((1 + d*x1*x2*y1*y2)*(1 - d*x1*x2*y1*y2) + d*(x1*y2 + y1*x2)*(y1*y2 + x1*x2)*x3*y3) := by
  linear_combination
    (-d^2 * x1 * x2^4 * y2^3 * x3^2 * y3 - d^2 * x1 * x2^3 * y2^4 * x3 * y3^2
      + d^2 * y1 * x2^4 * y2^3 * x3 * y3^2 + d^2 * y1 * x2^3 * y2^4 * x3^2 * y3
      - d * x1 * x2^4 * y2 * x3^2 * y3 - d * x1 * x2^3 * y2^2 * x3^3 - d * x1 * x2^3 * y2^2 * x3
      + d * x1 * x2^2 * y2^3 * y3^3 - d * x1 * x2^2 * y2^3 * y3 + d * x1 * x2 * y2^4 * x3 * y3^2
      + d * y1 * x2^4 * y2 * x3 * y3^2 + d * y1 * x2^3 * y2^2 * y3^3 - d * y1 * x2^3 * y2^2 * y3
      - d * y1 * x2^2 * y2^3 * x3^3 - d * y1 * x2^2 * y2^3 * x3 - d * y1 * x2 * y2^4 * x3^2 * y3) * h1 +
    (d^2 * x1^2 * y1 * x2^2 * y2 * x3^3 * y3^2 - d^2 * x1^2 * y1 * x2 * y2^2 * x3^2 * y3^3
      - d^2 * x1 * y1^2 * x2^2 * y2 * x3^2 * y3^3 + d^2 * x1 * y1^2 * x2 * y2^2 * x3^3 * y3^2
      + d * x1^3 * x2^2 * y2 * x3^2 * y3 + d * x1^3 * x2 * y2^2 * x3 * y3^2
      + d * x1^3 * x2 * x3^3 * y3^2 + d * x1^3 * y2 * x3^2 * y3^3
      - d * x1^2 * y1 * x2^2 * y2 * x3 * y3^2 - d * x1^2 * y1 * x2 * y2^2 * x3^2 * y3
      + d * x1^2 * y1 * x2 * x3^2 * y3^3 + d * x1^2 * y1 * y2 * x3^3 * y3^2
      - d * x1 * y1^2 * x2^2 * y2 * x3^2 * y3 - d * x1 * y1^2 * x2 * y2^2 * x3 * y3^2
      - d * x1 * y1^2 * x2 * x3^3 * y3^2 - d * x1 * y1^2 * y2 * x3^2 * y3^3
      + d * x1 * x2^2 * y2 * x3^2 * y3 + d * x1 * x2 * y2^2 * x3 * y3^2 + d * x1 * x2 * x3^3 * y3^2
      + d * x1 * y2 * x3^2 * y3^3 + d * y1^3 * x2^2 * y2 * x3 * y3^2
      + d * y1^3 * x2 * y2^2 * x3^2 * y3 - d * y1^3 * x2 * x3^2 * y3^3 - d * y1^3 * y2 * x3^3 * y3^2
      - d * y1 * x2^2 * y2 * x3 * y3^2 - d * y1 * x2 * y2^2 * x3^2 * y3 + d * y1 * x2 * x3^2 * y3^3
      + d * y1 * y2 * x3^3 * y3^2 + x1^3 * x2 * x3^3 - x1^3 * x2 * x3 * y3^2 + x1^3 * x2 * x3
      + x1^3 * y2 * x3^2 * y3 - x1^3 * y2 * y3^3 + x1^3 * y2 * y3 + x1^2 * y1 * x2 * x3^2 * y3
      - x1^2 * y1 * x2 * y3^3 + x1^2 * y1 * x2 * y3 + x1^2 * y1 * y2 * x3^3
      - x1^2 * y1 * y2 * x3 * y3^2 + x1^2 * y1 * y2 * x3 - x1 * y1^2 * x2 * x3^3
      + x1 * y1^2 * x2 * x3 * y3^2 - x1 * y1^2 * x2 * x3 - x1 * y1^2 * y2 * x3^2 * y3
      + x1 * y1^2 * y2 * y3^3 - x1 * y1^2 * y2 * y3 + x1 * x2 * x3^3 - x1 * x2 * x3 * y3^2
      + x1 * x2 * x3 + x1 * y2 * x3^2 * y3 - x1 * y2 * y3^3 + x1 * y2 * y3 - y1^3 * x2 * x3^2 * y3
      + y1^3 * x2 * y3^3 - y1^3 * x2 * y3 - y1^3 * y2 * x3^3 + y1^3 * y2 * x3 * y3^2
      - y1^3 * y2 * x3 + y1 * x2 * x3^2 * y3 - y1 * x2 * y3^3 + y1 * x2 * y3 + y1 * y2 * x3^3
      - y1 * y2 * x3 * y3^2 + y1 * y2 * x3) * h2 +
    (-d * x1^2 * y1 * x2^2 * y2 * x3 + d * x1^2 * y1 * x2 * y2^2 * y3 + d * x1 * y1^2 * x2^2 * y2 * y3
      - d * x1 * y1^2 * x2 * y2^2 * x3 - x1^3 * x2^3 * x3 - x1^3 * x2^2 * y2 * y3
      + x1^3 * x2 * y2^2 * x3 - x1^3 * x2 * x3 + x1^3 * y2^3 * y3 - x1^3 * y2 * y3
      - x1^2 * y1 * x2^3 * y3 - x1^2 * y1 * x2^2 * y2 * x3 + x1^2 * y1 * x2 * y2^2 * y3
      - x1^2 * y1 * x2 * y3 + x1^2 * y1 * y2^3 * x3 - x1^2 * y1 * y2 * x3 + x1 * y1^2 * x2^3 * x3
      + x1 * y1^2 * x2^2 * y2 * y3 - x1 * y1^2 * x2 * y2^2 * x3 + x1 * y1^2 * x2 * x3
      - x1 * y1^2 * y2^3 * y3 + x1 * y1^2 * y2 * y3 - x1 * x2^3 * x3 - x1 * x2^2 * y2 * y3
      + x1 * x2 * y2^2 * x3 - x1 * x2 * x3 + x1 * y2^3 * y3 - x1 * y2 * y3 + y1^3 * x2^3 * y3
      + y1^3 * x2^2 * y2 * x3 - y1^3 * x2 * y2^2 * y3 + y1^3 * x2 * y3 - y1^3 * y2^3 * x3
      + y1^3 * y2 * x3 - y1 * x2^3 * y3 - y1 * x2^2 * y2 * x3 + y1 * x2 * y2^2 * y3 - y1 * x2 * y3
      + y1 * y2^3 * x3 - y1 * y2 * x3) * h3

/-- Associativity, y-coordinate. -/
theorem assoc_y_poly (d x1 y1 x2 y2 x3 y3 : R) (h1 : -x1^2 + y1^2 = 1 + d*x1^2*y1^2) (h2 : -x2^2 + y2^2 = 1 + d*x2^2*y2^2) (h3 : -x3^2 + y3^2 = 1 + d*x3^2*y3^2) :
    ((y1*y2 + x1*x2)*(1 + d*x1*x2*y1*y2)*y3 + (x1*y2 + y1*x2)*(1 - d*x1*x2*y1*y2)*x3) * ((1 + d*x2*x3*y2*y3)*(1 - d*x2*x3*y2*y3) - d*x1*y1*(x2*y3 + y2*x3)*(y2*y3 + x2*x3)) =
      (y1*(y2*y3 + x2*x3)*(1 + d*x2*x3*y2*y3) + x1*(x2*y3 + y2*x3)*(1 - d*x2*x3*y2*y3)) * ((1 + d*x1*x2*y1*y2)*(1 - d*x1*x2*y1*y2) - d*(x1*y2 + y1*x2)*(y1*y2 + x1*x2)*x3*y3) := by
  linear_combination
    (d^2 * x1 * x2^4 * y2^3 * x3 * y3^2 + d^2 * x1 * x2^3 * y2^4 * x3^2 * y3
      - d^2 * y1 * x2^4 * y2^3 * x3^2 * y3 - d^2 * y1 * x2^3 * y2^4 * x3 * y3^2
      + d * x1 * x2^4 * y2 * x3 * y3^2 + d * x1 * x2^3 * y2^2 * y3^3 - d * x1 * x2^3 * y2^2 * y3
      - d * x1 * x2^2 * y2^3 * x3^3 - d * x1 * x2^2 * y2^3 * x3 - d * x1 * x2 * y2^4 * x3^2 * y3
      - d * y1 * x2^4 * y2 * x3^2 * y3 - d * y1 * x2^3 * y2^2 * x3^3 - d * y1 * x2^3 * y2^2 * x3
      + d * y1 * x2^2 * y2^3 * y3^3 - d * y1 * x2^2 * y2^3 * y3 + d * y1 * x2 * y2^4 * x3 * y3^2) * h1 +
    (d^2 * x1^2 * y1 * x2^2 * y2 * x3^2 * y3^3 - d^2 * x1^2 * y1 * x2 * y2^2 * x3^3 * y3^2
      - d^2 * x1 * y1^2 * x2^2 * y2 * x3^3 * y3^2 + d^2 * x1 * y1^2 * x2 * y2^2 * x3^2 * y3^3
      - d * x1^3 * x2^2 * y2 * x3 * y3^2 - d * x1^3 * x2 * y2^2 * x3^2 * y3
      + d * x1^3 * x2 * x3^2 * y3^3 + d * x1^3 * y2 * x3^3 * y3^2
      + d * x1^2 * y1 * x2^2 * y2 * x3^2 * y3 + d * x1^2 * y1 * x2 * y2^2 * x3 * y3^2
      + d * x1^2 * y1 * x2 * x3^3 * y3^2 + d * x1^2 * y1 * y2 * x3^2 * y3^3
      + d * x1 * y1^2 * x2^2 * y2 * x3 * y3^2 + d * x1 * y1^2 * x2 * y2^2 * x3^2 * y3
      - d * x1 * y1^2 * x2 * x3^2 * y3^3 - d * x1 * y1^2 * y2 * x3^3 * y3^2
      - d * x1 * x2^2 * y2 * x3 * y3^2 - d * x1 * x2 * y2^2 * x3^2 * y3 + d * x1 * x2 * x3^2 * y3^3
      + d * x1 * y2 * x3^3 * y3^2 - d * y1^3 * x2^2 * y2 * x3^2 * y3
      - d * y1^3 * x2 * y2^2 * x3 * y3^2 - d * y1^3 * x2 * x3^3 * y3^2 - d * y1^3 * y2 * x3^2 * y3^3
      + d * y1 * x2^2 * y2 * x3^2 * y3 + d * y1 * x2 * y2^2 * x3 * y3^2 + d * y1 * x2 * x3^3 * y3^2
      + d * y1 * y2 * x3^2 * y3^3 + x1^3 * x2 * x3^2 * y3 - x1^3 * x2 * y3^3 + x1^3 * x2 * y3
      + x1^3 * y2 * x3^3 - x1^3 * y2 * x3 * y3^2 + x1^3 * y2 * x3 + x1^2 * y1 * x2 * x3^3
      - x1^2 * y1 * x2 * x3 * y3^2 + x1^2 * y1 * x2 * x3 + x1^2 * y1 * y2 * x3^2 * y3
      - x1^2 * y1 * y2 * y3^3 + x1^2 * y1 * y2 * y3 - x1 * y1^2 * x2 * x3^2 * y3
      + x1 * y1^2 * x2 * y3^3 - x1 * y1^2 * x2 * y3 - x1 * y1^2 * y2 * x3^3
      + x1 * y1^2 * y2 * x3 * y3^2 - x1 * y1^2 * y2 * x3 + x1 * x2 * x3^2 * y3 - x1 * x2 * y3^3
      + x1 * x2 * y3 + x1 * y2 * x3^3 - x1 * y2 * x3 * y3^2 + x1 * y2 * x3 - y1^3 * x2 * x3^3
      + y1^3 * x2 * x3 * y3^2 - y1^3 * x2 * x3 - y1^3 * y2 * x3^2 * y3 + y1^3 * y2 * y3^3
      - y1^3 * y2 * y3 + y1 * x2 * x3^3 - y1 * x2 * x3 * y3^2 + y1 * x2 * x3 + y1 * y2 * x3^2 * y3
      - y1 * y2 * y3^3 + y1 * y2 * y3) * h2 +
    (-d * x1^2 * y1 * x2^2 * y2 * y3 + d * x1^2 * y1 * x2 * y2^2 * x3 + d * x1 * y1^2 * x2^2 * y2 * x3
      - d * x1 * y1^2 * x2 * y2^2 * y3 - x1^3 * x2^3 * y3 - x1^3 * x2^2 * y2 * x3
      + x1^3 * x2 * y2^2 * y3 - x1^3 * x2 * y3 + x1^3 * y2^3 * x3 - x1^3 * y2 * x3
      - x1^2 * y1 * x2^3 * x3 - x1^2 * y1 * x2^2 * y2 * y3 + x1^2 * y1 * x2 * y2^2 * x3
      - x1^2 * y1 * x2 * x3 + x1^2 * y1 * y2^3 * y3 - x1^2 * y1 * y2 * y3 + x1 * y1^2 * x2^3 * y3
      + x1 * y1^2 * x2^2 * y2 * x3 - x1 * y1^2 * x2 * y2^2 * y3 + x1 * y1^2 * x2 * y3
      - x1 * y1^2 * y2^3 * x3 + x1 * y1^2 * y2 * x3 - x1 * x2^3 * y3 - x1 * x2^2 * y2 * x3
      + x1 * x2 * y2^2 * y3 - x1 * x2 * y3 + x1 * y2^3 * x3 - x1 * y2 * x3 + y1^3 * x2^3 * x3
      + y1^3 * x2^2 * y2 * y3 - y1^3 * x2 * y2^2 * x3 + y1^3 * x2 * x3 - y1^3 * y2^3 * y3
      + y1^3 * y2 * y3 - y1 * x2^3 * x3 - y1 * x2^2 * y2 * y3 + y1 * x2 * y2^2 * x3 - y1 * x2 * x3
      + y1 * y2^3 * y3 - y1 * y2 * y3) * h3

/-- Montgomery doubling under `u = (1 + y)/(1 − y)`: with `y₂ = N/D` the `y` of `2P`,
`(1 + d)·y²·(D − N) = (1 − y²)·(1 + d·y²)·(D + N)`. -/
theorem mont_double_poly (d x1 y1 : R) (h1 : -x1^2 + y1^2 = 1 + d*x1^2*y1^2) :
    (1 + d) * y1^2 * ((1 - d*x1*x1*y1*y1) - (y1*y1 + x1*x1)) =
      (1 - y1^2) * (1 + d*y1^2) * ((1 - d*x1*x1*y1*y1) + (y1*y1 + x1*x1)) := by
  linear_combination
    (d * y1^4 + 1) * h1

/-- Montgomery differential addition under `u = (1 + y)/(1 − y)`: with `y(P₁+P₂) = N/D` and
`y(P₂−P₁) = N'/D'`, `(y₁+y₂)²·(D − N)·(D' − N') = (y₁−y₂)²·(D + N)·(D' + N')`. -/
theorem mont_diffadd_poly (d x1 y1 x2 y2 : R) (h1 : -x1^2 + y1^2 = 1 + d*x1^2*y1^2) (h2 : -x2^2 + y2^2 = 1 + d*x2^2*y2^2) :
    (y1 + y2)^2 * ((1 - d*x1*x2*y1*y2) - (y1*y2 + x1*x2)) * ((1 + d*x2*x1*y2*y1) - (y2*y1 - x2*x1)) =
      (y1 - y2)^2 * ((1 - d*x1*x2*y1*y2) + (y1*y2 + x1*x2)) * ((1 + d*x2*x1*y2*y1) + (y2*y1 - x2*x1)) := by
  linear_combination
    (4 * d * y1 * x2^2 * y2^3 + 4 * y1 * x2^2 * y2) * h1 +
    (4 * y1^3 * y2 - 4 * y1 * y2) * h2

end TlsMpcProofs.Edwards
