/-!
Sealed-sender key agreement with an additively shared scalar and a masked
private point (design: `handshake_backend/EmpHybridWork/SEALED_SENDER_AGREEMENT.md`).

Setting: an abelian group of points written additively with integer scalar
multiplication (`Lean.Grind.IntModule`), a base point `B`, a private recipient
point `R` held only as shares by the engines, and two parties A and B.

  K_A = kA·B, K_B = kB·B          published (commit, then open)
  M_A, M_B                         private mask points, honestly mA·B, mB·B
  Z = R + M_A + M_B                opened to both parties
  U_A = kA·Z, C_A = (kA·mA)·B + mA·K_B      supplied privately by A
  U_B = kB·Z, C_B = (kB·mB)·B + mB·K_A      supplied privately by B
  D = U_A + U_B − C_A − C_B        computed by the engines, never opened

What is proved (algebra only; everything computational is stated, not proved):

* `agreement_correct`: with honest parties, `D = (kA + kB)·R`.
* `mask_hides`: the opened `Z` is the same for a different recipient point and
  a correspondingly shifted honest mask, so `Z` carries no information about
  `R` for a party that does not know the other party's (uniform) mask.
* `other_contribution`: for ARBITRARY points `M_A`, `K_A` chosen by a deviating
  party A, the honest party's contribution is
  `U_B − C_B = kB·R + kB·M_A − mB·K_A`.
* `guess_attack`: if A may choose its mask freely, the choice
  `M_A = a·B − R'` makes that contribution computable from A's own values and
  public points whenever the guess `R'` is right. Together with the envelope's
  MAC this would let A test one guess per message. This is why masks must come
  with a proof of knowledge of their discrete logarithm.
* `contribution_with_known_logs`: once A's mask and public share are known
  multiples of the base point (`M_A = a·B`, `K_A = c·B`, as a knowledge proof
  guarantees), `D = (terms A can compute from its view) + (kB + c)·R`. Checking
  a guess `R'` against the envelope therefore requires `(kB + c)·R'`, a
  Diffie–Hellman value of the public point `K_B + c·B` with `R'`.
* `proof_extracts` and `proof_hides`: the cut-and-choose knowledge proof for a
  hidden mask. Two accepting answers to the two challenges on one commitment
  yield the discrete logarithm; the value opened for challenge 1 is the same
  for any other mask with a correspondingly shifted commitment.

Not proved here: that Diffie–Hellman values are hard to compute; that the
envelope reveals nothing beyond a way to check a candidate `D` (key derivation
and MAC as random oracles); soundness amplification over repeated challenges;
and that commit-then-open makes the public shares independent.
-/
namespace TlsMpc.MaskedAgreement
open Lean.Grind

variable {G : Type} [IntModule G]

/-- The point both parties see. -/
def opened (R maskA maskB : G) : G := R + maskA + maskB

/-- What the engines compute from the four privately supplied points. -/
def combine (uA cA uB cB : G) : G := uA + uB - cA - cB

theorem smul_exchange (a b : Int) (x : G) : a • (b • x) = b • (a • x) := by
  rw [← IntModule.mul_zsmul, Int.mul_comm, IntModule.mul_zsmul]

theorem agreement_correct (B R : G) (kA kB mA mB : Int) :
    combine (kA • opened R (mA • B) (mB • B)) ((kA * mA) • B + mA • (kB • B))
        (kB • opened R (mA • B) (mB • B)) ((kB * mB) • B + mB • (kA • B)) =
      (kA + kB) • R := by
  simp only [combine, opened, IntModule.zsmul_add, IntModule.add_zsmul, IntModule.mul_zsmul]
  rw [smul_exchange mA kB B, smul_exchange mB kA B]
  grind

theorem mask_hides (R other maskA maskB : G) :
    opened R maskA maskB = opened other maskA (maskB + R - other) := by
  simp only [opened]
  grind

/-- The honest party's contribution for arbitrary points chosen by the other. -/
theorem other_contribution (B R maskA shareA : G) (kB mB : Int) :
    kB • opened R maskA (mB • B) - ((kB * mB) • B + mB • shareA) =
      kB • R + kB • maskA - mB • shareA := by
  simp only [opened, IntModule.zsmul_add, IntModule.mul_zsmul]
  grind

/-- With a freely chosen mask `a·B − guess`, a correct guess removes the
recipient point from the honest party's contribution. -/
theorem guess_attack (B R : G) (a c kB mB : Int) :
    kB • opened R (a • B - R) (mB • B) - ((kB * mB) • B + mB • (c • B)) =
      a • (kB • B) - c • (mB • B) := by
  simp only [opened, IntModule.zsmul_add, IntModule.zsmul_sub, IntModule.mul_zsmul]
  rw [smul_exchange kB a B, smul_exchange mB c B]
  grind

/-- With known discrete logarithms of the deviating party's mask and share, the
result is a part computable from that party's view plus `(kB + c)·R`. Here
`Z = opened R (a·B) (mB·B)` is the opened point and `offset` is whatever the
deviating party supplied for its own two points. -/
theorem contribution_with_known_logs (B R offset : G) (a c kB mB : Int) :
    offset + (kB • opened R (a • B) (mB • B) - ((kB * mB) • B + mB • (c • B))) =
      (offset + a • (kB • B) - c • opened R (a • B) (mB • B) + (c * a) • B) + (kB + c) • R := by
  simp only [opened, IntModule.zsmul_add, IntModule.add_zsmul, IntModule.mul_zsmul]
  rw [smul_exchange kB a B, smul_exchange mB c B]
  grind

/-! ### Knowledge proof for a hidden mask (one round)

The prover commits to `W = w·B` (private input), the challenge is a public bit,
and the prover publishes `z`. For challenge 0 the engines open `W`; for
challenge 1 they open `W + M`; in both cases the opened point must equal `z·B`. -/

theorem proof_extracts (B W M : G) (z0 z1 : Int) (zero : z0 • B = W) (one : z1 • B = W + M) :
    M = (z1 - z0) • B := by
  rw [IntModule.sub_zsmul, zero, one]
  grind

theorem proof_hides (W M other : G) : W + M = (W + M - other) + other := by
  grind

#print axioms agreement_correct
#print axioms mask_hides
#print axioms other_contribution
#print axioms guess_attack
#print axioms contribution_with_known_logs
#print axioms proof_extracts

end TlsMpc.MaskedAgreement
