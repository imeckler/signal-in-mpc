import Std

/-!
Functional contract for backend-owned share refresh.

`Shares` denotes the entire committee's shares in a mathematical model. It is
not a runtime value that a party is allowed to assemble. A production adapter
holds only its own component.

The laws below are explicit assumptions about a linear sharing scheme. This
file does not instantiate Shamir sharing, certify an MP-SPDZ implementation,
prove confidentiality, model randomness, or prove proactive security. In
particular, the theorem about `normalize` says nothing about freshness: its
input must be generated with fresh sharing randomness by the backend.

`normalize` is NOT the proposed proactive backend protocol. A native Shamir
public opening can reveal all shares of the random polynomial, and therefore
its zero-mask coefficients, to each participant. The required proactive design
instead keeps jointly generated mask coefficients secret and privately outputs
only each recipient's own delta. See `specs/sharing-refresh.json`.
-/

namespace TlsMpc.Sharing

/-- The algebraic obligations used by the functional refresh proof. -/
structure LinearSharing (Shares Value : Type) where
  valid : Shares → Prop
  value : Shares → Value
  zero : Value
  addValue : Value → Value → Value
  subValue : Value → Value → Value
  addShares : Shares → Shares → Shares
  subShares : Shares → Shares → Shares
  publicShares : Value → Shares
  public_valid : ∀ x, valid (publicShares x)
  public_value : ∀ x, value (publicShares x) = x
  add_valid : ∀ x y, valid x → valid y → valid (addShares x y)
  sub_valid : ∀ x y, valid x → valid y → valid (subShares x y)
  add_value : ∀ x y, valid x → valid y →
    value (addShares x y) = addValue (value x) (value y)
  sub_value : ∀ x y, valid x → valid y →
    value (subShares x y) = subValue (value x) (value y)
  add_zero : ∀ x, addValue x zero = x
  sub_self : ∀ x, subValue x x = zero

namespace LinearSharing

variable (scheme : LinearSharing Shares Value)

/-- A valid sharing whose reconstructed value is zero; no entropy claim. -/
structure ZeroSharing where
  shares : Shares
  valid : scheme.valid shares
  value_zero : scheme.value shares = scheme.zero

/--
Subtract the public sharing of a random sharing's checked opening.

The backend must check the opening before using it. Here `scheme.value random`
is the mathematical result of that opening. This is `[r] - public(r)`, not
`[r] - [r]`. Whether the result has fresh sharing randomness is a separate
backend/security obligation.
-/
def normalize (random : Shares) (h : scheme.valid random) : scheme.ZeroSharing where
  shares := scheme.subShares random (scheme.publicShares (scheme.value random))
  valid := scheme.sub_valid _ _ h (scheme.public_valid _)
  value_zero := by
    rw [scheme.sub_value _ _ h (scheme.public_valid _), scheme.public_value,
      scheme.sub_self]

def refresh (old : Shares) (mask : scheme.ZeroSharing) : Shares :=
  scheme.addShares old mask.shares

theorem refresh_valid (old : Shares) (h : scheme.valid old)
    (mask : scheme.ZeroSharing) : scheme.valid (scheme.refresh old mask) :=
  scheme.add_valid _ _ h mask.valid

theorem refresh_preserves_value (old : Shares) (h : scheme.valid old)
    (mask : scheme.ZeroSharing) :
    scheme.value (scheme.refresh old mask) = scheme.value old := by
  rw [refresh, scheme.add_value _ _ h mask.valid, mask.value_zero, scheme.add_zero]

theorem normalized_refresh_preserves_value (old random : Shares)
    (hold : scheme.valid old) (hrandom : scheme.valid random) :
    scheme.value (scheme.refresh old (scheme.normalize random hrandom)) =
      scheme.value old :=
  scheme.refresh_preserves_value old hold _

/-- Each object receives its own mask argument. Independence is not encoded. -/
def refreshBatch {n : Nat} (old : Fin n → Shares)
    (masks : Fin n → scheme.ZeroSharing) : Fin n → Shares :=
  fun i => scheme.refresh (old i) (masks i)

theorem refreshBatch_preserves_values {n : Nat} (old : Fin n → Shares)
    (valid : ∀ i, scheme.valid (old i)) (masks : Fin n → scheme.ZeroSharing) :
    (fun i => scheme.value (scheme.refreshBatch old masks i)) =
      (fun i => scheme.value (old i)) := by
  funext i
  exact scheme.refresh_preserves_value (old i) (valid i) (masks i)

end LinearSharing

/-!
Exact byte packing is independent of a sharing scheme. A 256-bit key must not
be reduced modulo a smaller prime when imported. This lossless two-limb model
uses a 248-bit lower limb and an 8-bit upper limb; both fit the proposed
Curve25519 computation field. Range checks and cross-domain conversion still
belong to the compiler/backend interface.
-/

structure KeyLimbs where
  low : Fin (2 ^ 248)
  high : Fin (2 ^ 8)

def packKey (key : Fin (2 ^ 256)) : KeyLimbs where
  low := ⟨key.val % (2 ^ 248), Nat.mod_lt _ (by decide)⟩
  high := ⟨key.val / (2 ^ 248), by
    have hk := key.isLt
    omega⟩

def unpackKey (limbs : KeyLimbs) : Nat :=
  limbs.low.val + (2 ^ 248) * limbs.high.val

theorem unpack_packKey (key : Fin (2 ^ 256)) :
    unpackKey (packKey key) = key.val := by
  simp only [unpackKey, packKey]
  exact Nat.mod_add_div _ _

theorem packKey_injective : Function.Injective packKey := by
  intro a b h
  apply Fin.ext
  have := congrArg unpackKey h
  simpa only [unpack_packKey] using this

theorem keyLimbs_fit_curve25519 (limbs : KeyLimbs) :
    limbs.low.val < 2 ^ 255 - 19 ∧ limbs.high.val < 2 ^ 255 - 19 := by
  have hlo := limbs.low.isLt
  have hhi := limbs.high.isLt
  constructor <;> omega

end TlsMpc.Sharing
