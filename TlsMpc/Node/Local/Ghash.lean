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

/-! ### The multiplication the controller runs

`Ghash.concrete.maskBit x i` builds a 128-bit mask with `BitVec.replicate` (128 one-bit appends),
256 times per product: a record's half took about 0.1 s (PERFORMANCE.md, "The script path's cost").
`mulFast` is the same algorithm with `maskAnd` (the selected bit decides between `v` and 0) instead
of the mask (`mul_eq_mulFast`); the IO glue computes with `halfFastOf`, `leftsFastOf`,
`extendFastOf` (below), which are `halfOf`, `leftsOf`, `extendOf` with `mulFast` (`halfFast_eq`,
`lefts_fast_eq`, `extendFast_eq`). `mul` itself, and everything proved about it, is unchanged. -/

/-- `concrete.and (concrete.maskBit x i) v`, without building the mask (`maskAnd_eq`). -/
def maskAnd (x : W) (i : Nat) (v : W) : W := if x.getLsbD i then v else Ghash.concrete.const 0

theorem maskAnd_eq (x : W) (i : Nat) (v : W) :
    Ghash.concrete.and (Ghash.concrete.maskBit x i) v = maskAnd x i v := by
  simp only [Ghash.concrete, maskAnd]
  ext j hj
  rw [BitVec.getElem_and, BitVec.getElem_replicate]
  by_cases h : x.getLsbD i
  · simp only [h, if_true, Nat.mod_one]
    simp [h]
  · simp only [h, Nat.mod_one]
    simp [h]

/-- `Ghash.nextPower Ghash.concrete` with `maskAnd`. -/
def nextPowerFast (v : W) : W :=
  Ghash.concrete.xor (Ghash.concrete.shr v) (maskAnd v 0 (Ghash.concrete.const Ghash.reduction))

/-- `Ghash.powers Ghash.concrete` with `nextPowerFast`. -/
def powersFast : Nat → W → List W
  | 0, _ => []
  | n + 1, v => v :: powersFast n (nextPowerFast v)

/-- `Ghash.multiplyLoop Ghash.concrete` with `maskAnd`. -/
def loopFast (x : W) : List W → Nat → W → W
  | [], _, z => z
  | v :: rest, i, z => loopFast x rest (i + 1) (Ghash.concrete.xor z (maskAnd x (127 - i) v))

/-- `mul`, computed without the masks. -/
def mulFast (x y : W) : W := loopFast x (powersFast 128 y) 0 (Ghash.concrete.const 0)

theorem nextPowerFast_eq (v : W) : nextPowerFast v = Ghash.nextPower Ghash.concrete v := by
  simp only [nextPowerFast, Ghash.nextPower, maskAnd_eq]

theorem powersFast_eq (n : Nat) (v : W) : powersFast n v = Ghash.powers Ghash.concrete n v := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp only [powersFast, Ghash.powers, ih, nextPowerFast_eq]

theorem loopFast_eq (x : W) (l : List W) (i : Nat) (z : W) :
    loopFast x l i z = Ghash.multiplyLoop Ghash.concrete x l i z := by
  induction l generalizing i z with
  | nil => rfl
  | cons v rest ih => simp only [loopFast, Ghash.multiplyLoop, ih, maskAnd_eq]

/-- **`mulFast` is `mul`.** -/
theorem mul_eq_mulFast : @mul = @mulFast := by
  funext x y
  simp only [mul, mulFast, Ghash.multiply, Ghash.multiplyPrepared, powersFast_eq, loopFast_eq]

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

/-! ### The same, computed with `mulFast` (what the IO glue runs) -/

/-- `half` with `mulFast`. -/
def halfFast (shares : List W) (aad ct : B8) : W :=
  GhashShares.localTag mulFast (blocks aad ct) ((shares.take (blocks aad ct).length).reverse)

theorem halfFast_eq (shares : List W) (aad ct : B8) : halfFast shares aad ct = half shares aad ct := by
  simp only [halfFast, half, mul_eq_mulFast]

/-- `extend` with `mulFast` (its squares). -/
def extendFast (base : List W) (t : Nat) (odd : List W) : List W :=
  base ++ (List.range (t - base.length)).map fun i =>
    if (base.length + 1 + i) % 2 = 0 then mulFast (base.getD ((base.length + 1 + i) / 2 - 1) 0)
      (base.getD ((base.length + 1 + i) / 2 - 1) 0)
    else odd.getD (i / 2) 0

theorem extendFast_eq (base : List W) (t : Nat) (odd : List W) : extendFast base t odd = extend base t odd := by
  simp only [extendFast, extend, square, mul_eq_mulFast]

/-- `lefts` with `mulFast`. -/
def leftsFast (base : List W) (t : Nat) : List W :=
  (oddPowers base.length t).map fun k => mulFast (base.getD ((k - 1) / 2 - 1) 0) (base.getD ((k - 1) / 2 - 1) 0)

theorem lefts_fast_eq (base : List W) (t : Nat) : leftsFast base t = lefts base t := by
  simp only [leftsFast, lefts]
  apply List.map_congr_left
  intro k _
  simp only [left, square, mul_eq_mulFast]

def halfFastOf (shares : Secret (List W)) (aad ct : B8) : Secret W := shares.map (halfFast · aad ct)
def leftsFastOf (shares : Secret (List W)) (t : Nat) : Secret (List W) := shares.map (leftsFast · t)
def extendFastOf (shares : Secret (List W)) (t : Nat) (odd : Secret (List W)) : Secret (List W) :=
  Secret.zipWith (fun b o => extendFast b t o) shares odd

theorem halfFastOf_eq (shares : Secret (List W)) (aad ct : B8) : halfFastOf shares aad ct = halfOf shares aad ct := by
  simp only [halfFastOf, halfOf, halfFast_eq]

theorem leftsFastOf_eq (shares : Secret (List W)) (t : Nat) : leftsFastOf shares t = leftsOf shares t := by
  simp only [leftsFastOf, leftsOf, lefts_fast_eq]

theorem extendFastOf_eq (shares : Secret (List W)) (t : Nat) (odd : Secret (List W)) :
    extendFastOf shares t odd = extendOf shares t odd := by
  simp only [extendFastOf, extendOf, extendFast_eq]

/-! ### The multiplication on two 64-bit limbs (what the IO glue runs, 2026-11-13, later)

`mulFast` still works on `BitVec 128`, an arbitrary-precision number: each of its ~1,000 shifts,
XORs and bit tests per product allocates, and a record's GHASH glue (the doubling rounds' squares
and left inputs, then this party's half: about 200 products per record) cost ~40 ms of the
controller's time per message (PERFORMANCE.md, "The script path's cost", second round). `mulL` is the
same algorithm (the same `powers` table and loop, `Ghash.multiply`) on `L`, two `UInt64` limbs; `L.toW`
maps every step to `mulFast`'s (`toW_xorL`, `toW_shrL`, `bitL_eq`, the two constants), so
`mulLimb x y := (mulL (L.ofW x) (L.ofW y)).toW` IS `mul` (`mul_eq_mulLimb`). The glue computes
`halfLimbOf` / `leftsLimbOf` / `extendLimbOf`, each proved equal to `halfOf` / `leftsOf` /
`extendOf`. Nothing proved about `mul` changed. -/

/-- A GF(2¹²⁸) element as two 64-bit limbs of its `BitVec 128`: `hi` = bits 127…64, `lo` = 63…0. -/
structure L where
  hi : UInt64
  lo : UInt64

def L.toW (x : L) : W := x.hi.toBitVec ++ x.lo.toBitVec

def L.ofW (w : W) : L := ⟨UInt64.ofBitVec (w.extractLsb' 64 64), UInt64.ofBitVec (w.extractLsb' 0 64)⟩

theorem L.toW_ofW (w : W) : (L.ofW w).toW = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [L.toW, L.ofW, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : i < 64
  · simp [h]
  · have e : 64 + (i - 64) = i := by omega
    have l : i - 64 < 64 := by omega
    simp [h, e, l]

def xorL (a b : L) : L := ⟨a.hi ^^^ b.hi, a.lo ^^^ b.lo⟩

theorem toW_xorL (a b : L) : (xorL a b).toW = a.toW ^^^ b.toW := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [L.toW, xorL, BitVec.getLsbD_append, BitVec.getLsbD_xor, UInt64.toBitVec_xor]
  split <;> rfl

/-- `Ghash.concrete.shr` (one place toward bit 0) on the limbs. -/
def shrL (a : L) : L := ⟨a.hi >>> 1, (a.lo >>> 1) ||| (a.hi <<< 63)⟩

theorem toW_shrL (a : L) : (shrL a).toW = a.toW.extractLsb' 1 128 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [L.toW, shrL, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h1 : i < 63
  · have h2 : i < 64 := by omega
    have h3 : 1 + i < 64 := by omega
    simp [h1, h2, h3, hi]
  · by_cases h2 : i < 64
    · have h4 : i = 63 := by omega
      subst h4
      simp
    · have h3 : ¬ 1 + i < 64 := by omega
      have e : 1 + (i - 64) = 1 + i - 64 := by omega
      simp [h2, h3, hi, e]

/-- Bit `i < 64` of a word, without leaving machine arithmetic. -/
def bit64 (v : UInt64) (i : Nat) : Bool := (v >>> UInt64.ofNat i) &&& 1 != 0

theorem bit64_eq (v : UInt64) (i : Nat) (hi : i < 64) : bit64 v i = v.toBitVec.getLsbD i := by
  have h64 : i % 2 ^ 64 = i := Nat.mod_eq_of_lt (by omega)
  have h : ((v >>> UInt64.ofNat i) &&& 1).toNat = v.toNat >>> i % 2 := by
    simp [UInt64.toNat_and, UInt64.toNat_shiftRight, UInt64.toNat_ofNat, h64, Nat.mod_eq_of_lt hi,
      Nat.and_one_is_mod]
  simp only [bit64, BitVec.getLsbD, Nat.testBit, UInt64.toNat_toBitVec]
  rcases Nat.mod_two_eq_zero_or_one (v.toNat >>> i) with h2 | h2
  · have e : ((v >>> UInt64.ofNat i) &&& 1) = 0 := UInt64.toNat_inj.mp (by rw [h, h2]; rfl)
    rw [e]
    simp [h2]
  · have e : ((v >>> UInt64.ofNat i) &&& 1) = 1 := UInt64.toNat_inj.mp (by rw [h, h2]; rfl)
    rw [e]
    simp [h2]

/-- Bit `i` of the element (`getLsbD` of `toW`, `bitL_eq`). -/
def bitL (x : L) (i : Nat) : Bool :=
  if i < 64 then bit64 x.lo i else if i < 128 then bit64 x.hi (i - 64) else false

theorem bitL_eq (x : L) (i : Nat) : bitL x i = x.toW.getLsbD i := by
  simp only [bitL, L.toW, BitVec.getLsbD_append]
  by_cases h1 : i < 64
  · simp [h1, bit64_eq _ _ h1]
  · by_cases h2 : i < 128
    · simp [h1, h2, bit64_eq _ (i - 64) (by omega)]
    · simp only [h1, h2, if_false]
      rw [BitVec.getLsbD_of_ge]
      omega

def zeroL : L := ⟨0, 0⟩
def reductionL : L := ⟨0xe100000000000000, 0⟩

theorem toW_zeroL : zeroL.toW = Ghash.concrete.const 0 := by decide
theorem toW_reductionL : reductionL.toW = Ghash.concrete.const Ghash.reduction := by decide

/-- `nextPowerFast` on the limbs. -/
def nextPowerL (v : L) : L := xorL (shrL v) (if bitL v 0 then reductionL else zeroL)

/-- `powersFast` on the limbs. -/
def powersL : Nat → L → List L
  | 0, _ => []
  | n + 1, v => v :: powersL n (nextPowerL v)

/-- `loopFast` on the limbs. -/
def loopL (x : L) : List L → Nat → L → L
  | [], _, z => z
  | v :: rest, i, z => loopL x rest (i + 1) (xorL z (if bitL x (127 - i) then v else zeroL))

/-- `mulFast` on the limbs. -/
def mulL (x y : L) : L := loopL x (powersL 128 y) 0 zeroL

/-- `mul`, computed on the limbs. -/
def mulLimb (x y : W) : W := (mulL (L.ofW x) (L.ofW y)).toW

theorem toW_select (c : Bool) (v : L) (x : W) (i : Nat) (h : c = x.getLsbD i) :
    (if c then v else zeroL).toW = maskAnd x i v.toW := by
  simp only [maskAnd, ← h]
  cases c <;> simp [toW_zeroL]

theorem toW_nextPowerL (v : L) : (nextPowerL v).toW = nextPowerFast v.toW := by
  simp only [nextPowerL, nextPowerFast, toW_xorL, toW_shrL,
    toW_select _ _ v.toW 0 (bitL_eq v 0), toW_reductionL]
  rfl

theorem powersL_map (n : Nat) (v : L) : (powersL n v).map L.toW = powersFast n v.toW := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp only [powersL, powersFast, List.map_cons, ih, toW_nextPowerL]

theorem loopL_toW (x : L) (l : List L) (i : Nat) (z : L) :
    (loopL x l i z).toW = loopFast x.toW (l.map L.toW) i z.toW := by
  induction l generalizing i z with
  | nil => rfl
  | cons v rest ih =>
    simp only [loopL, loopFast, List.map_cons, ih, toW_xorL, toW_select _ _ x.toW (127 - i) (bitL_eq x _)]
    rfl

theorem mulL_toW (x y : L) : (mulL x y).toW = mulFast x.toW y.toW := by
  simp only [mulL, mulFast, loopL_toW, powersL_map, toW_zeroL]

theorem mulLimb_eq (x y : W) : mulLimb x y = mulFast x y := by
  simp only [mulLimb, mulL_toW, L.toW_ofW]

/-- **`mulLimb` is `mul`.** -/
theorem mul_eq_mulLimb : @mul = @mulLimb := by
  funext x y
  rw [mulLimb_eq, mul_eq_mulFast]

/-- `half` with `mulLimb`. -/
def halfLimb (shares : List W) (aad ct : B8) : W :=
  GhashShares.localTag mulLimb (blocks aad ct) ((shares.take (blocks aad ct).length).reverse)

theorem halfLimb_eq (shares : List W) (aad ct : B8) : halfLimb shares aad ct = half shares aad ct := by
  simp only [halfLimb, half, mul_eq_mulLimb]

/-- `extend` with `mulLimb` (its squares). -/
def extendLimb (base : List W) (t : Nat) (odd : List W) : List W :=
  base ++ (List.range (t - base.length)).map fun i =>
    if (base.length + 1 + i) % 2 = 0 then mulLimb (base.getD ((base.length + 1 + i) / 2 - 1) 0)
      (base.getD ((base.length + 1 + i) / 2 - 1) 0)
    else odd.getD (i / 2) 0

theorem extendLimb_eq (base : List W) (t : Nat) (odd : List W) : extendLimb base t odd = extend base t odd := by
  simp only [extendLimb, extend, square, mul_eq_mulLimb]

/-- `lefts` with `mulLimb`. -/
def leftsLimb (base : List W) (t : Nat) : List W :=
  (oddPowers base.length t).map fun k => mulLimb (base.getD ((k - 1) / 2 - 1) 0) (base.getD ((k - 1) / 2 - 1) 0)

theorem leftsLimb_eq (base : List W) (t : Nat) : leftsLimb base t = lefts base t := by
  simp only [leftsLimb, lefts]
  apply List.map_congr_left
  intro k _
  simp only [left, square, mul_eq_mulLimb]

def halfLimbOf (shares : Secret (List W)) (aad ct : B8) : Secret W := shares.map (halfLimb · aad ct)
def leftsLimbOf (shares : Secret (List W)) (t : Nat) : Secret (List W) := shares.map (leftsLimb · t)
def extendLimbOf (shares : Secret (List W)) (t : Nat) (odd : Secret (List W)) : Secret (List W) :=
  Secret.zipWith (fun b o => extendLimb b t o) shares odd

theorem halfLimbOf_eq (shares : Secret (List W)) (aad ct : B8) : halfLimbOf shares aad ct = halfOf shares aad ct := by
  simp only [halfLimbOf, halfOf, halfLimb_eq]

theorem leftsLimbOf_eq (shares : Secret (List W)) (t : Nat) : leftsLimbOf shares t = leftsOf shares t := by
  simp only [leftsLimbOf, leftsOf, leftsLimb_eq]

theorem extendLimbOf_eq (shares : Secret (List W)) (t : Nat) (odd : Secret (List W)) :
    extendLimbOf shares t odd = extendOf shares t odd := by
  simp only [extendLimbOf, extendOf, extendLimb_eq]

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
