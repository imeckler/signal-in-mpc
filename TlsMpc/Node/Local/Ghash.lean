import TlsMpc.GcmShareKernelsProofs
import TlsMpc.Node.Secret

/-!
# Each node's local GF(2¹²⁸) arithmetic on its own GHASH key-power shares

REORGANIZATION_PLAN.md stage S12 (`Local/Ghash.lean`; P-GHASH, section 7.1). Replaces the local
part of `handshake_backend/EmpHybridWork/gcm_shares.h`: `gf_multiply` (lines 21-30), the squaring
of even powers in `GcmShares::ensure` (line 50) and `GcmShares::half` (lines 60-71). The engine part
(the resharing kernels `gcm-key-share`, `gcm-multiply`) is `Flows/Ghash.lean`.

WHAT IS HERE (executable; no I/O; no emitter imports this module).
  * `mul`: GF(2¹²⁸) multiplication in GCM's bit order, DEFINED as the repository's
    `Ghash.multiply Ghash.concrete` (the one the kernels and `GhashField.laws` are about), so there
    is nothing to relate: the C++ `gf_multiply` is gone with this file.
  * `blocks`: a record's GHASH blocks, `Gcm.authInput` (the header as associated data, the
    ciphertext, the two bit lengths); `needed`: their number (`GcmShares::blocks`).
  * `half shares aad ct`: this party's half of the tag polynomial, `⊕ᵢ blockᵢ · share(H^(count−i))`,
    DEFINED as `GhashShares.localTag mul (blocks aad ct)` on the first `count` shares reversed: the
    form `shared_halves_are_ghash_proved` consumes.
  * `extend base t odd`: one round of the DOUBLING schedule. From shares of H¹ … Hᵐ (`base`, m ≥ 1)
    to shares of H¹ … Hᵗ (t ≤ 2m): an even power H^k is the square of this party's share of
    H^(k/2) (squaring is additive in characteristic 2); an odd power comes from the engines (`odd`,
    in the order of `oddPowers m t`: A's fresh masks for A, the opened masked products for B). The
    engines' input for odd k is `left base k`, this party's share of H^(k−1) (a square, computed
    here), times the share of H¹. A deviation from the C++ order (`GcmShares::ensure`, one engine
    round per odd power, each a full agreement round): every odd power of a round in ONE
    `gcm-multiply` run with `copies` (Flows/Ghash.lean), so H¹ … Hⁿ take ⌈log₂ n⌉ + 1 rounds instead
    of about n / 2.
  * `Secret` versions (`halfOf`, `extendOf`, `leftsOf`): the same functions under `Secret.map`; they
    never look inside.

PROVED (standard axioms only; no evaluation of a multiplication):
  * `Shared a b h n` (A's list `a`, B's list `b` XOR to H¹ … Hⁿ position by position) and
    P-GHASH (a) for this schedule: `shared_start` (one resharing of H) and `shared_extend` (a round,
    given that each odd power's two engine values XOR to the product of the two parties' inputs:
    what `gcm-multiply` and its opening give, `GcmShareKernelsProofs.gcmMultiply_reshare`).
  * P-GHASH (b) and the form (c) needs: `halves_xor` (the two halves XOR to `ghashOf`, GCM's GHASH
    of the header and ciphertext under `H = hashKeyOf traffic`, whenever the shares are `Shared`
    for `H` with enough powers), from `shared_halves_are_ghash_proved` and `shared_descending`.
  * `half_eq_localTag`: `half` is `localTag` over `Gcm.authInput` (definitional; stated so that the
    restatements name it).
-/

namespace TlsMpc.Node.Local.Ghash

open TlsMpc

abbrev W := BitVec 128
abbrev B8 := List (BitVec 8)

/-! ## Field arithmetic -/

/-- GF(2¹²⁸) multiplication in GCM's bit order (NIST SP 800-38D algorithm 1; the C++
`gf_multiply`): the repository's `Ghash.multiply Ghash.concrete`. -/
def mul (x y : W) : W := Ghash.multiply Ghash.concrete x y

/-- Squaring (each party squares its own share of an even power's half). -/
def square (x : W) : W := mul x x

/-- A 16-byte block as a field element (`Gcm.concrete.pack`). -/
def ofBytes (b : B8) : W := Gcm.concrete.pack b

/-- A field element as its 16 bytes (`Gcm.concrete.unpack`). -/
def toBytes (w : W) : B8 := Gcm.concrete.unpack w

theorem ofBytes_toBytes (w : W) : ofBytes (toBytes w) = w := HybridKernel.pack_unpack w

theorem toBytes_length (w : W) : (toBytes w).length = 16 := by
  simp [toBytes, Gcm.concrete, Ghash.unpackValue]

/-! ## The tag polynomial -/

/-- A record's GHASH blocks: the header (associated data) and the ciphertext, each padded to 16
bytes, then their bit lengths (`Gcm.authInput`). -/
def blocks (aad ct : B8) : List W := Gcm.authInput Gcm.concrete aad ct

/-- How many key powers a record with `aad` header bytes and `ct` ciphertext bytes needs
(`GcmShares::blocks`). -/
def needed (aad ct : Nat) : Nat := (aad + 15) / 16 + (ct + 15) / 16 + 1

/-- **This party's half of the tag polynomial** (`GcmShares::half`): `⊕ᵢ blockᵢ · sᵢ`, block `i`
matched with this party's share of `H^(count−i)` (the first `count` shares, reversed). -/
def half (shares : List W) (aad ct : B8) : W :=
  GhashShares.localTag mul (blocks aad ct) ((shares.take (blocks aad ct).length).reverse)

theorem half_eq_localTag (shares : List W) (aad ct : B8) :
    half shares aad ct = GhashShares.localTag (Ghash.multiply Ghash.concrete) (Gcm.authInput Gcm.concrete aad ct)
      ((shares.take (Gcm.authInput Gcm.concrete aad ct).length).reverse) := rfl

/-! ## The doubling schedule -/

/-- The first odd power above `m`. -/
def firstOdd (m : Nat) : Nat := if (m + 1) % 2 = 1 then m + 1 else m + 2

/-- How many odd powers lie in `(m, t]`. -/
def oddCount (m t : Nat) : Nat := if firstOdd m ≤ t then (t - firstOdd m) / 2 + 1 else 0

/-- The odd powers a round from `m` to `t` powers computes in the engines, in order: the odd `k`
with `m < k ≤ t`. -/
def oddPowers (m t : Nat) : List Nat := (List.range (oddCount m t)).map fun j => firstOdd m + 2 * j

theorem length_oddPowers (m t : Nat) : (oddPowers m t).length = oddCount m t := by simp [oddPowers]

/-- Element `i / 2` of the odd powers is power `m + 1 + i`, for every odd power of the round. -/
theorem oddPowers_getD (m t i : Nat) (hi : i < t - m) (ho : (m + 1 + i) % 2 = 1) :
    i / 2 < oddCount m t ∧ (oddPowers m t).getD (i / 2) 0 = m + 1 + i := by
  have hc : i / 2 < oddCount m t := by
    simp only [oddCount, firstOdd]
    split <;> split <;> omega
  refine ⟨hc, ?_⟩
  simp only [oddPowers, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hc,
    Option.map_some, Option.getD_some, firstOdd]
  split <;> omega

/-- This party's share of `H^(k−1)` for an odd `k ≥ 3`: the square of its share of `H^((k−1)/2)`
(index `(k−1)/2 − 1`). The left input of the engines' product for power `k`. -/
def left (base : List W) (k : Nat) : W := square (base.getD ((k - 1) / 2 - 1) 0)

/-- The left inputs of a round, in the order of `oddPowers`. -/
def lefts (base : List W) (t : Nat) : List W := (oddPowers base.length t).map (left base)

theorem length_lefts (base : List W) (t : Nat) : (lefts base t).length = oddCount base.length t := by
  simp [lefts, length_oddPowers]

theorem lefts_getD (base : List W) (t i : Nat) (hi : i < t - base.length)
    (ho : (base.length + 1 + i) % 2 = 1) :
    (lefts base t).getD (i / 2) 0 = left base (base.length + 1 + i) := by
  obtain ⟨hc, he⟩ := oddPowers_getD base.length t i hi ho
  have hl : i / 2 < (oddPowers base.length t).length := by rw [length_oddPowers]; exact hc
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some] at he
  simp only [lefts, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl,
    Option.map_some, Option.getD_some, he]

/-- **One round of the schedule**: shares of `H¹ … Hᵐ` (`m = base.length`) extended to `H¹ … Hᵗ`.
Element `i` of the new part is power `k = m + 1 + i`: even `k`, the square of the share of
`H^(k/2)`; odd `k`, the engines' value number `i / 2` (the odd powers of the round, in order). -/
def extend (base : List W) (t : Nat) (odd : List W) : List W :=
  base ++ (List.range (t - base.length)).map fun i =>
    if (base.length + 1 + i) % 2 = 0 then square (base.getD ((base.length + 1 + i) / 2 - 1) 0)
    else odd.getD (i / 2) 0

theorem extend_length (base : List W) (t : Nat) (odd : List W) (h : base.length ≤ t) :
    (extend base t odd).length = t := by
  simp [extend]
  omega

/-- The next round's target: double, capped at `n`. -/
def nextTarget (m n : Nat) : Nat := min (2 * m) n

/-! ## Secret versions (no look inside) -/

/-- This party's half, from its secret shares. -/
def halfOf (shares : Secret (List W)) (aad ct : B8) : Secret W := shares.map (half · aad ct)

/-- This party's left inputs of a round, from its secret shares. -/
def leftsOf (shares : Secret (List W)) (t : Nat) : Secret (List W) := shares.map (lefts · t)

/-- A round's result, from this party's secret shares and its secret engine values. -/
def extendOf (shares : Secret (List W)) (t : Nat) (odd : Secret (List W)) : Secret (List W) :=
  Secret.zipWith (fun b o => extend b t o) shares odd

/-! ## P-GHASH (a): the two parties' shares XOR to the key powers -/

/-- `H^(k+1)` (`GhashShares.power`, the repository multiplication). -/
abbrev power (h : W) (k : Nat) : W := GhashShares.power mul h k

/-- A's list `a` and B's list `b` are XOR shares of `H¹ … Hⁿ`, position `k` holding `H^(k+1)`. -/
def Shared (a b : List W) (h : W) (n : Nat) : Prop :=
  a.length = n ∧ b.length = n ∧ ∀ k, k < n → a.getD k 0 ^^^ b.getD k 0 = power h k

theorem laws : GhashShares.Laws mul := GhashField.laws

theorem additive : GhashShares.KeyAdditive mul := GhashShares.multiply_key_additive

theorem square_xor (x y : W) : square x ^^^ square y = square (x ^^^ y) :=
  (GhashShares.square_additive mul laws additive x y).symm

theorem power_mul (h : W) (i j : Nat) : mul (power h i) (power h j) = power h (i + j + 1) :=
  HybridKernel.Schedule.power_mul mul laws h i j

theorem xor_unmask (a b : W) : a ^^^ (b ^^^ a) = b := HybridKernel.Schedule.xor_unmask a b

/-- **The first share** (`gcm-key-share`): A keeps its mask, B holds `H ⊕ mask`. -/
theorem shared_start (h mask : W) : Shared [mask] [h ^^^ mask] h 1 := by
  refine ⟨rfl, rfl, fun k hk => ?_⟩
  have : k = 0 := by omega
  subst this
  exact xor_unmask mask h

/-- **One round keeps the sharing** (P-GHASH (a) for the doubling schedule). From shares of
`H¹ … Hᵐ` (`m ≥ 1`) and, for every odd power `k` of the round, engine values whose XOR is the product
of the two parties' left inputs and their shares of `H¹` (what `gcm-multiply` reshares), the
extended lists are shares of `H¹ … Hᵗ`, for any `t` with `m ≤ t ≤ 2m`. Uses commutativity and
associativity (`GhashField.laws`) and additivity (`multiply_key_additive`); nothing is evaluated. -/
theorem shared_extend (a b : List W) (h : W) (m t : Nat) (oa ob : List W)
    (hs : Shared a b h m) (hm : 1 ≤ m) (hmt : m ≤ t) (ht : t ≤ 2 * m)
    (hodd : ∀ i, i < t - m → (m + 1 + i) % 2 = 1 →
      oa.getD (i / 2) 0 ^^^ ob.getD (i / 2) 0 =
        mul (left a (m + 1 + i) ^^^ left b (m + 1 + i)) (a.getD 0 0 ^^^ b.getD 0 0)) :
    Shared (extend a t oa) (extend b t ob) h t := by
  obtain ⟨la, lb, hk⟩ := hs
  refine ⟨by rw [extend_length _ _ _ (by omega)], by rw [extend_length _ _ _ (by omega)], ?_⟩
  intro k hkt
  by_cases hkm : k < m
  · have ea : (extend a t oa).getD k 0 = a.getD k 0 := by
      simp only [extend, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    have eb : (extend b t ob).getD k 0 = b.getD k 0 := by
      simp only [extend, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rw [ea, eb]
    exact hk k hkm
  · obtain ⟨i, rfl⟩ : ∃ i, k = m + i := ⟨k - m, by omega⟩
    have hi : i < t - m := by omega
    have ga : (extend a t oa).getD (m + i) 0 =
        if (m + 1 + i) % 2 = 0 then square (a.getD ((m + 1 + i) / 2 - 1) 0) else oa.getD (i / 2) 0 := by
      simp only [extend, List.getD_eq_getElem?_getD, la]
      rw [List.getElem?_append_right (by omega)]
      simp [la, hi]
    have gb : (extend b t ob).getD (m + i) 0 =
        if (m + 1 + i) % 2 = 0 then square (b.getD ((m + 1 + i) / 2 - 1) 0) else ob.getD (i / 2) 0 := by
      simp only [extend, List.getD_eq_getElem?_getD, lb]
      rw [List.getElem?_append_right (by omega)]
      simp [lb, hi]
    rw [ga, gb]
    split
    · next he =>
      -- even power k = m + 1 + i: squares of the shares of H^(k/2)
      rw [square_xor, square, hk _ (by omega), power_mul]
      congr 1
      omega
    · next ho =>
      have ho' : (m + 1 + i) % 2 = 1 := by omega
      rw [hodd i hi ho', left, left, square_xor, square, hk _ (by omega), hk 0 hm, power_mul, power_mul]
      congr 1
      omega

/-! ## P-GHASH (b), and the halves hypothesis of `sealCtr_with_tag_is_seal` (c) -/

theorem take_getD (l : List W) (c k : Nat) (hk : k < c) : (l.take c).getD k 0 = l.getD k 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hk, if_true]

/-- Shared shares, cut to the first `count` powers and reversed (highest power first), XOR to the
descending powers `GhashShares.descending` (hypothesis (2) of `shared_halves_are_ghash`). -/
theorem shared_descending (a b : List W) (h : W) (n count : Nat) (hs : Shared a b h n) (hc : count ≤ n) :
    List.zipWith (· ^^^ ·) (a.take count).reverse (b.take count).reverse =
      GhashShares.descending mul h count := by
  obtain ⟨la, lb, hk⟩ := hs
  have lta : (a.take count).length = count := by simp [la]; omega
  have ltb : (b.take count).length = count := by simp [lb]; omega
  rw [HybridKernel.Schedule.descending_eq, ← List.reverse_zipWith (by rw [lta, ltb])]
  congr 1
  apply List.ext_getElem
  · simp [lta, ltb]
  · intro k h1 h2
    simp only [List.length_zipWith, lta, ltb, Nat.min_self] at h1
    rw [List.getElem_zipWith, List.getElem_map, List.getElem_range]
    have e1 := take_getD a count k h1
    have e2 := take_getD b count k h1
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [lta]; exact h1),
      List.getElem?_eq_getElem (by rw [ltb]; exact h1), Option.getD_some] at e1 e2
    rw [e1, e2]
    exact hk k (by omega)

/-- **P-GHASH (b) and (c)'s hypothesis.** When A's shares `a` and B's shares `b` are XOR shares of
`H¹ … Hⁿ` for the GHASH key of the traffic block (`H = hashKeyOf traffic = AES_K(0¹²⁸)`) and `n`
covers the record's blocks, the bytes of the two halves XOR to GCM's GHASH value of the header and
ciphertext (`ghashOf`): exactly the hypothesis `halves` of `sealCtr_with_tag_is_seal`. -/
theorem halves_xor (traffic aad ct : B8) (a b : List W) (n : Nat)
    (hs : Shared a b (HybridKernel.hashKeyOf traffic) n) (hn : (blocks aad ct).length ≤ n) :
    Aes.addRoundKey Gcm.concrete.aes (toBytes (half a aad ct)) (toBytes (half b aad ct)) =
      HybridKernel.ghashOf traffic aad ct :=
  HybridKernel.shared_halves_are_ghash_proved traffic aad ct _ _
    (by simp only [List.length_reverse, List.length_take]; rw [hs.1, hs.2.1])
    (shared_descending a b _ n _ hs hn)

/-- The number of blocks is `needed` of the lengths. -/
theorem blocks_length (aad ct : B8) : (blocks aad ct).length =
    (aad.length + (16 - aad.length % 16) % 16 + (ct.length + (16 - ct.length % 16) % 16) + 16) / 16 := by
  simp [blocks, Gcm.authInput, Gcm.blocks, Gcm.pad16, Gcm.zeros, Gcm.encodeNat]
  omega

end TlsMpc.Node.Local.Ghash
