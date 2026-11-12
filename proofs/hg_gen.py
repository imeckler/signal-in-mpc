"""Generate proofs/TlsMpcProofs/EdwardsPoly.lean: the polynomial identities behind the Edwards
group law, each proved by `linear_combination` with explicit cofactors of the curve equations.
The cofactors are found here by rewriting d*x_i^2*y_i^2 -> y_i^2 - x_i^2 - 1 (hg_poly.reduce);
Lean checks them, so nothing here is trusted."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hg_poly import *

OUT = '/Users/izzy/repos/tls-mpc/proofs/TlsMpcProofs/EdwardsPoly.lean'

d, x1, y1, x2, y2, x3, y3 = V('d', 'x1', 'y1', 'x2', 'y2', 'x3', 'y3')


def pair(xa, ya, xb, yb):
    dl = xa * xb * ya * yb
    return xa * yb + ya * xb, ya * yb + xa * xb, 1 + d * dl, 1 - d * dl


def spair(a, b):
    return (f'(x{a}*y{b} + y{a}*x{b})', f'(y{a}*y{b} + x{a}*x{b})',
            f'(1 + d*x{a}*x{b}*y{a}*y{b})', f'(1 - d*x{a}*x{b}*y{a}*y{b})')


X12, Y12, Dx12, Dy12 = pair(x1, y1, x2, y2)
X23, Y23, Dx23, Dy23 = pair(x2, y2, x3, y3)
sX12, sY12, sDx12, sDy12 = spair(1, 2)
sX23, sY23, sDx23, sDy23 = spair(2, 3)

items = []

# closure
items.append(dict(
    name='closure_poly', pts=(1, 2),
    doc='Closure: the sum of two curve points satisfies the curve equation, denominators cleared.',
    lhs=f'-{sX12}^2*{sDy12}^2 + {sY12}^2*{sDx12}^2',
    rhs=f'{sDx12}^2*{sDy12}^2 + d*{sX12}^2*{sY12}^2',
    N=-X12 ** 2 * Dy12 ** 2 + Y12 ** 2 * Dx12 ** 2 - Dx12 ** 2 * Dy12 ** 2 - d * X12 ** 2 * Y12 ** 2))

NLx = X12 * Dy12 * y3 + Y12 * Dx12 * x3
DLx = Dx12 * Dy12 + d * X12 * Y12 * x3 * y3
NLy = Y12 * Dx12 * y3 + X12 * Dy12 * x3
DLy = Dx12 * Dy12 - d * X12 * Y12 * x3 * y3
NRx = x1 * Y23 * Dx23 + y1 * X23 * Dy23
DRx = Dx23 * Dy23 + d * x1 * y1 * X23 * Y23
NRy = y1 * Y23 * Dx23 + x1 * X23 * Dy23
DRy = Dx23 * Dy23 - d * x1 * y1 * X23 * Y23

items.append(dict(
    name='assoc_x_poly', pts=(1, 2, 3),
    doc='Associativity, x-coordinate: numerator of `(P₁+P₂)+P₃` times denominator of `P₁+(P₂+P₃)` '
        'equals the converse, modulo the three curve equations.',
    lhs=f'({sX12}*{sDy12}*y3 + {sY12}*{sDx12}*x3) * ({sDx23}*{sDy23} + d*x1*y1*{sX23}*{sY23})',
    rhs=f'(x1*{sY23}*{sDx23} + y1*{sX23}*{sDy23}) * ({sDx12}*{sDy12} + d*{sX12}*{sY12}*x3*y3)',
    N=NLx * DRx - NRx * DLx))

items.append(dict(
    name='assoc_y_poly', pts=(1, 2, 3),
    doc='Associativity, y-coordinate.',
    lhs=f'({sY12}*{sDx12}*y3 + {sX12}*{sDy12}*x3) * ({sDx23}*{sDy23} - d*x1*y1*{sX23}*{sY23})',
    rhs=f'(y1*{sY23}*{sDx23} + x1*{sX23}*{sDy23}) * ({sDx12}*{sDy12} - d*{sX12}*{sY12}*x3*y3)',
    N=NLy * DRy - NRy * DLy))

# Montgomery x-only formulas under u = (1 + y)/(1 - y)
N11 = y1 * y1 + x1 * x1
Dm11 = 1 - d * x1 * x1 * y1 * y1
items.append(dict(
    name='mont_double_poly', pts=(1,),
    doc='Montgomery doubling under `u = (1 + y)/(1 − y)`: with `y₂ = N/D` the `y` of `2P`,\n'
        '`(1 + d)·y²·(D − N) = (1 − y²)·(1 + d·y²)·(D + N)`.',
    lhs='(1 + d) * y1^2 * ((1 - d*x1*x1*y1*y1) - (y1*y1 + x1*x1))',
    rhs='(1 - y1^2) * (1 + d*y1^2) * ((1 - d*x1*x1*y1*y1) + (y1*y1 + x1*x1))',
    N=(1 + d) * y1 ** 2 * (Dm11 - N11) - (1 - y1 ** 2) * (1 + d * y1 ** 2) * (Dm11 + N11)))

NS = y1 * y2 + x1 * x2
DS = 1 - d * x1 * x2 * y1 * y2
ND = y2 * y1 - x2 * x1
DD = 1 + d * x2 * x1 * y2 * y1
items.append(dict(
    name='mont_diffadd_poly', pts=(1, 2),
    doc='Montgomery differential addition under `u = (1 + y)/(1 − y)`: with `y(P₁+P₂) = N/D` and\n'
        '`y(P₂−P₁) = N\'/D\'`, `(y₁+y₂)²·(D − N)·(D\' − N\') = (y₁−y₂)²·(D + N)·(D\' + N\')`.',
    lhs='(y1 + y2)^2 * ((1 - d*x1*x2*y1*y2) - (y1*y2 + x1*x2)) * ((1 + d*x2*x1*y2*y1) - (y2*y1 - x2*x1))',
    rhs='(y1 - y2)^2 * ((1 - d*x1*x2*y1*y2) + (y1*y2 + x1*x2)) * ((1 + d*x2*x1*y2*y1) + (y2*y1 - x2*x1))',
    N=(y1 + y2) ** 2 * (DS - NS) * (DD - ND) - (y1 - y2) ** 2 * (DS + NS) * (DD + ND)))

HEADER = '''import Mathlib.Tactic.LinearCombination
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
'''


def main():
    out = [HEADER]
    for it in items:
        r = best_reduce(it['N'], it['pts'])
        assert r is not None, it['name']
        k, cof, order = r
        assert k == 0
        pts = it['pts']
        vars_ = ' '.join(f'x{i} y{i}' for i in pts)
        hyps = ' '.join(f'(h{i} : -x{i}^2 + y{i}^2 = 1 + d*x{i}^2*y{i}^2)' for i in pts)
        combo = []
        for i in pts:
            c = -cof[i]
            if not c.is_zero():
                combo.append(f'    ({c.lean()}) * h{i}')
        out.append(f"/-- {it['doc']} -/")
        out.append(f"theorem {it['name']} (d {vars_} : R) {hyps} :")
        out.append(f"    {it['lhs']} =\n      {it['rhs']} := by")
        out.append('  linear_combination\n' + ' +\n'.join(combo))
        out.append('')
        print(it['name'], 'cofactor terms', {i: len(cof[i]) for i in pts})
    out.append('end TlsMpcProofs.Edwards\n')
    with open(OUT, 'w') as f:
        f.write('\n'.join(out))
    print('wrote', OUT)


if __name__ == '__main__':
    main()
