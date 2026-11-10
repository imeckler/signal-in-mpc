/-!
Sealed-sender key agreement by a public offset from a per-conversation secret
key (design: `handshake_backend/EmpHybridWork/SEALED_SENDER_AGREEMENT.md`,
recommended variant).

Once per conversation the engines compute, with the shared-scalar ladder, a
secret scalar `k₀` (known to nobody), the public point `K₀ = k₀·B`, the shared
point `k₀·R`, and a table of shared multiples of the private recipient point
`R`. For each message the two parties jointly sample an offset `τ` that both of
them know and the server does not. The message's ephemeral public key is
`K₀ + τ·B` (computed in the clear); its agreement is `k₀·R + τ·R`, where `τ·R`
is a sum of table entries chosen by the digits of `τ` (inside the engines).

No point is ever supplied by a party, so there is nothing for a deviating party
to choose: the attack on the masked variant (`MaskedAgreement.guess_attack`)
has no counterpart here.

Proved (algebra, in any abelian group with integer scalars):

* `public_key_correct`, `agreement_correct`: the pair is the Diffie–Hellman
  pair of the scalar `k₀ + τ`.
* `table_sum_correct`: the sum of table entries selected by the digits of the
  offset is the offset's multiple of `R`.
* `public_key_independent`: for any other initial scalar the same public key
  arises from a correspondingly shifted offset. With the offset uniform and
  unknown to the server, the sequence of public keys is therefore distributed
  independently of `k₀` and of each other: nothing links two messages.
* `candidate_needs_initial`: the agreement for a candidate recipient point
  differs from a value the parties can compute (`τ` times the candidate) by
  exactly `k₀` times the candidate, which is a Diffie–Hellman value of the
  public `K₀` with the candidate.

Not proved: hardness of Diffie–Hellman; that the opened envelope reveals only
a way to check a candidate agreement (key derivation and MAC as random
oracles); that an offset drawn from `[0, 2^252)` is statistically close to
uniform modulo the group order; and correctness of the point-addition field
programs with respect to the curve's group law.
-/
namespace TlsMpc.OffsetAgreement
open Lean.Grind

variable {G : Type} [IntModule G]

theorem public_key_correct (B : G) (initial offset : Int) :
    initial • B + offset • B = (initial + offset) • B := by
  rw [IntModule.add_zsmul]

theorem agreement_correct (R : G) (initial offset : Int) :
    initial • R + offset • R = (initial + offset) • R := by
  rw [IntModule.add_zsmul]

/-- The offset written in base 16, least significant digit first, starting at
weight `16^position`. -/
def offsetValue : Nat → List Int → Int
  | _, [] => 0
  | position, digit :: rest => digit * 16 ^ position + offsetValue (position + 1) rest

/-- Sum of the table entries `(digit · 16^position)·R` selected by the digits. -/
def tableSum (R : G) : Nat → List Int → G
  | _, [] => 0
  | position, digit :: rest => (digit * 16 ^ position) • R + tableSum R (position + 1) rest

theorem table_sum_correct (R : G) (position : Nat) (digits : List Int) :
    tableSum R position digits = offsetValue position digits • R := by
  induction digits generalizing position with
  | nil => simp only [tableSum, offsetValue, IntModule.zero_zsmul]
  | cons digit rest ih => simp only [tableSum, offsetValue, IntModule.add_zsmul, ih]

theorem public_key_independent (B : G) (initial other offset : Int) :
    initial • B + offset • B = other • B + (offset + initial - other) • B := by
  rw [IntModule.sub_zsmul, IntModule.add_zsmul]
  grind

theorem candidate_needs_initial (candidate : G) (initial offset : Int) :
    (initial + offset) • candidate - offset • candidate = initial • candidate := by
  rw [IntModule.add_zsmul]
  grind

#print axioms table_sum_correct
#print axioms public_key_independent
#print axioms candidate_needs_initial

end TlsMpc.OffsetAgreement
