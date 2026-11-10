import Std.Tactic

namespace EmpHybrid

/-- Canonical representative of x-r in Fp, with x,r already canonical. -/
def masked (p x r : Nat) : Nat := if x < r then x + p - r else x - r
/-- One conditional subtraction suffices when both summands are canonical. -/
def recovered (p r c : Nat) : Nat := if r + c < p then r + c else r + c - p

theorem masked_range (p x r : Nat) (hx : x < p) (hr : r < p) :
    masked p x r < p := by
  unfold masked
  split <;> omega

theorem recovered_range (p r c : Nat) (hr : r < p) (hc : c < p) :
    recovered p r c < p := by
  unfold recovered
  split <;> omega

/-- Backend-independent value invariant; not a circuit or security proof. -/
theorem masked_recovered (p x r : Nat) (hx : x < p) (hr : r < p) :
    recovered p r (masked p x r) = x := by
  unfold masked recovered
  split <;> split <;> omega

/-- For fixed x, the masked representatives determine r uniquely. This is
    the finite-domain injectivity needed in the uniform-mask argument. -/
theorem masked_injective (p x r s : Nat) (_hx : x < p)
    (hr : r < p) (hs : s < p) (h : masked p x r = masked p x s) : r = s := by
  unfold masked at h
  split at h <;> split at h <;> omega

/-- Boolean-to-field decoding with a checked shared mask. -/
def bitToField (maskedBit r : Bool) : Nat :=
  if maskedBit then 1 - (if r then 1 else 0) else (if r then 1 else 0)

theorem bit_mask_decode (b r : Bool) :
    bitToField (b != r) r = (if b then 1 else 0) := by
  cases b <;> cases r <;> rfl

#print axioms masked_range
#print axioms recovered_range
#print axioms masked_recovered
#print axioms masked_injective
#print axioms bit_mask_decode
end EmpHybrid
