import TlsMpc.WordMask
import TlsMpc.X25519Fast

/-!
Boolean circuit deriving the swap-bit inputs of `X25519Fast` from the 256 scalar
bits (bit `i` weighing `2^i`). It has no AND gates: adjacent bits are XORed where
XOR is free, so the field program spends no product on them.

Output `k` (for `0 ≤ k < 252`) is the swap bit of ladder step `k + 2`.
-/
namespace TlsMpc.X25519SwapBits
open BoolDag WordMask

def swapBit (t : Nat) : Expr :=
  if t = 2 then .input 3
  else if t = 253 then not' (.input 253)
  else xor' (.input (t + 1)) (.input t)

def circuit : List Expr := (List.range 252).map (fun k => swapBit (k + 2))

theorem swapBit_eval (env : Nat → Bool) (t : Nat) (h2 : 2 ≤ t) (h : t ≤ 253) :
    (swapBit t).eval env = X25519Fast.swapBitSpec env t := by
  unfold swapBit
  split
  · rename_i ht
    subst ht
    rw [X25519Fast.swapBitSpec_bottom]
    rfl
  · split
    · rename_i _ ht
      subst ht
      rw [X25519Fast.swapBitSpec_top, not'_eval]
      rfl
    · rw [X25519Fast.swapBitSpec_interior env t (by omega) (by omega), xor'_eval]
      rfl

/-- XOR shares: each party applies the same map to its own share of the scalar,
and exactly one party complements step 253. Share-wise results XOR to the swap
bits of the XORed scalar. -/
theorem swapBit_shares (a b : Nat → Bool) (t : Nat) (h3 : 3 ≤ t) (h : t ≤ 252) :
    X25519Fast.swapBitSpec (fun i => a i ^^ b i) t =
      ((a (t + 1) ^^ a t) ^^ (b (t + 1) ^^ b t)) := by
  rw [X25519Fast.swapBitSpec_interior _ t h3 h]
  cases a (t + 1) <;> cases a t <;> cases b (t + 1) <;> cases b t <;> rfl

#print axioms swapBit_eval
#print axioms swapBit_shares

end TlsMpc.X25519SwapBits
