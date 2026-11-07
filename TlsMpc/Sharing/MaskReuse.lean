import Std

/-!
Algebraic explanation of the repeated-mask attack, with arbitrary epoch masks.

This integer model proves cancellation and the three-point reconstruction
identity symbolically. It is not a finite-field Shamir implementation or a
security proof of the experimental PRZS backend. The native regression checks
the attack using the actual Fp25519 and CCD extension-field arithmetic. The
exposure schedule is the clean-transition rotating schedule already admitted
by `Sharing/Epoch.lean`: no three simultaneous compromises are needed.
-/

namespace TlsMpc.Sharing.MaskReuse

def commonEpoch (initial : Int) (masks : Nat → Int) : Nat → Int
  | 0 => initial
  | e + 1 => commonEpoch initial masks e + masks e

theorem common_mask_difference (left right : Int) (masks : Nat → Int) (epoch : Nat) :
    commonEpoch left masks epoch - commonEpoch right masks epoch = left - right := by
  induction epoch with
  | zero => rfl
  | succ epoch ih =>
      simp only [commonEpoch]
      omega

def quadratic (c0 c1 c2 x : Int) : Int := c0 + c1 * x + c2 * x * x

theorem three_point_reconstruction (c0 c1 c2 : Int) :
    3 * quadratic c0 c1 c2 1 - 3 * quadratic c0 c1 c2 2 +
      quadratic c0 c1 c2 3 = c0 := by
  simp only [quadratic]
  omega

def differenceObservation (a0 a1 a2 b0 b1 b2 : Int)
    (masks : Nat → Int → Int) (epoch : Nat) (point : Int) : Int :=
  commonEpoch (quadratic a0 a1 a2 point) (fun e => masks e point) epoch -
    commonEpoch (quadratic b0 b1 b2 point) (fun e => masks e point) epoch

/-- Three different parties sampled in three different epochs recover a relation. -/
theorem three_epoch_difference (a0 a1 a2 b0 b1 b2 : Int)
    (masks : Nat → Int → Int) :
    3 * differenceObservation a0 a1 a2 b0 b1 b2 masks 0 1 -
      3 * differenceObservation a0 a1 a2 b0 b1 b2 masks 1 2 +
      differenceObservation a0 a1 a2 b0 b1 b2 masks 2 3 = a0 - b0 := by
  simp only [differenceObservation, common_mask_difference, quadratic]
  omega

/-- A known zero reference turns the relation into the other record's value. -/
theorem known_reference_recovers_value (a0 a1 a2 b1 b2 : Int)
    (masks : Nat → Int → Int) :
    3 * differenceObservation a0 a1 a2 0 b1 b2 masks 0 1 -
      3 * differenceObservation a0 a1 a2 0 b1 b2 masks 1 2 +
      differenceObservation a0 a1 a2 0 b1 b2 masks 2 3 = a0 := by
  simpa using three_epoch_difference a0 a1 a2 0 b1 b2 masks

/-- Polynomial used by the experimental excluded-party subset construction. -/
def subsetBasis (excluded point : Int) : Int := point * (point - excluded)

theorem subset_basis_zero (excluded : Int) : subsetBasis excluded 0 = 0 := by
  simp [subsetBasis]

theorem subset_basis_excluded (excluded : Int) : subsetBasis excluded excluded = 0 := by
  simp [subsetBasis]

end TlsMpc.Sharing.MaskReuse
