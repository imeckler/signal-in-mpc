import TlsMpcProofs.MontgomeryLadder

/-!
# The clamped X25519 scalar as a closed formula (RFC 7748 `decodeScalar25519`)

`MontgomeryLadder.clampedScalar input` is the big-endian value of the 255 bits
`X25519.scalarSpec input 254, …, 0` that the ladder visits. Here:

* `clampedScalar_eq`: for any bit function, `clampedScalar input = 2²⁵⁴ + 8·m` with `m` the value
  of the input bits 3 … 253 (bits 0–2 cleared, bit 254 set, bit 255 ignored);
* `clampedScalar_testBit`: for the bits of a number `n`, `clampedScalar = 2²⁵⁴ + 8·(⌊n/8⌋ mod 2²⁵¹)`;
* `clampedScalar_decodeScalar`: for the 32 bytes as the program reads them
  (`X25519.decodeScalar`, bit `i` of byte `i/8`), it is the RFC 7748 clamped integer of the
  little-endian value `n` of the bytes: `2²⁵⁴ + 8·(⌊n/8⌋ mod 2²⁵¹)`, i.e. `n` with the low three
  bits cleared, bit 255 cleared and bit 254 set (`k[0] &= 248; k[31] &= 127; k[31] |= 64`);
* consequences: `clampedScalar input` is a multiple of 8 and lies in `[2²⁵⁴, 2²⁵⁵)`
  (`clampedScalar_mod_eight`, `clampedScalar_range`).
-/

namespace TlsMpcProofs.Ed25519
open TlsMpc X25519

theorem bitsValue_cons (n : ℕ) (b : Bool) (l : List Bool) :
    bitsValue n (b :: l) = bitsValue (2 * n + b.toNat) l := rfl

theorem bitsValue_append_single (n : ℕ) (l : List Bool) (b : Bool) :
    bitsValue n (l ++ [b]) = 2 * bitsValue n l + b.toNat := by
  induction l generalizing n with
  | nil => rfl
  | cons a rest ih => exact ih (2 * n + a.toNat)

theorem bitsValue_lt (l : List Bool) : bitsValue 0 l < 2 ^ l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [bitsValue]
  | append_singleton l b ih =>
    rw [bitsValue_append_single, List.length_append, List.length_singleton, pow_succ]
    have : b.toNat ≤ 1 := Bool.toNat_le b
    omega

/-- The bits the ladder visits: `254`, then `253 … 3` from the input, then three zeros. -/
theorem scalarBits_eq (input : ℕ → Bool) :
    (List.range 255).reverse.map (scalarSpec input) =
      true :: ((List.range 251).reverse.map (fun i => input (i + 3)) ++ [false, false, false]) := by
  have hr : (List.range 255).reverse =
      254 :: (((List.range 251).map (fun x => 3 + x)).reverse ++ [2, 1, 0]) := by
    rw [show (255 : ℕ) = 254 + 1 from rfl, List.range_succ, List.reverse_append,
      show (254 : ℕ) = 3 + 251 from rfl, List.range_add, List.reverse_append]
    rfl
  rw [hr, List.map_cons, List.map_append]
  have h254 : scalarSpec input 254 = true := by simp [scalarSpec]
  have hlow : [2, 1, 0].map (scalarSpec input) = [false, false, false] := by simp [scalarSpec]
  rw [h254, hlow, List.map_reverse, List.map_map, ← List.map_reverse]
  have hm : (List.range 251).reverse.map (scalarSpec input ∘ fun x => 3 + x) =
      (List.range 251).reverse.map (fun i => input (i + 3)) := by
    apply List.map_congr_left
    intro i hi
    have hi' : i < 251 := List.mem_range.mp (List.mem_reverse.mp hi)
    simp only [Function.comp_apply, scalarSpec]
    rw [if_neg (by omega), if_neg (by omega), Nat.add_comm]
  rw [hm]

/-- **The clamped scalar, for any input bits:** `2²⁵⁴ + 8·m`, `m` the value of input bits
3 … 253. -/
theorem clampedScalar_eq (input : ℕ → Bool) :
    clampedScalar input =
      2 ^ 254 + 8 * bitsValue 0 ((List.range 251).reverse.map (fun i => input (i + 3))) := by
  unfold clampedScalar
  rw [scalarBits_eq, bitsValue_cons, bitsValue_eq, show [false, false, false] = [false] ++ [false] ++ [false] from rfl,
    ← List.append_assoc, ← List.append_assoc, bitsValue_append_single, bitsValue_append_single,
    bitsValue_append_single]
  simp only [List.length_append, List.length_map, List.length_reverse, List.length_range,
    List.length_cons, List.length_nil, Bool.toNat_true, Bool.toNat_false]
  ring

/-- **For the bits of a number `n`:** `clampedScalar = 2²⁵⁴ + 8·(⌊n/8⌋ mod 2²⁵¹)`. -/
theorem clampedScalar_testBit (n : ℕ) :
    clampedScalar (fun i => n.testBit i) = 2 ^ 254 + 8 * (n / 8 % 2 ^ 251) := by
  have hm : (List.range 251).reverse.map (fun i => n.testBit (i + 3)) =
      (List.range 251).reverse.map (fun i => (n / 8).testBit i) := by
    apply List.map_congr_left
    intro i _
    rw [show n / 8 = n >>> 3 by rw [Nat.shiftRight_eq_div_pow], Nat.testBit_shiftRight,
      Nat.add_comm]
  rw [clampedScalar_eq, hm, bitsValue_testBits]

/-- Little-endian value of a byte string. -/
def leValue : List UInt8 → ℕ
  | [] => 0
  | b :: rest => b.toNat + 256 * leValue rest

/-- `X25519.decodeScalar` reads bit `i` of the little-endian value of the bytes. -/
theorem decodeScalar_eq_testBit (bytes : List UInt8) (i : ℕ) :
    decodeScalar bytes i = (leValue bytes).testBit i := by
  induction bytes generalizing i with
  | nil => simp [decodeScalar, leValue]
  | cons b rest ih =>
    have hb : b.toNat < 2 ^ 8 := b.toNat_lt
    have e : leValue (b :: rest) = 2 ^ 8 * leValue rest + b.toNat := by
      simp only [leValue]; ring
    rw [e, Nat.testBit_two_pow_mul_add _ hb]
    unfold decodeScalar
    by_cases hi : i < 8
    · rw [if_pos hi, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
      rfl
    · rw [if_neg hi, ← ih (i - 8)]
      unfold decodeScalar
      have h1 : i / 8 = (i - 8) / 8 + 1 := by omega
      have h2 : i % 8 = (i - 8) % 8 := by omega
      rw [h1, h2]
      rfl

/-- **RFC 7748 clamping:** for the scalar bytes as the program reads them, the ladder's scalar is
`2²⁵⁴ + 8·(⌊n/8⌋ mod 2²⁵¹)` for `n` the little-endian value of the bytes: the low three bits
cleared, bit 255 cleared, bit 254 set. -/
theorem clampedScalar_decodeScalar (bytes : List UInt8) :
    clampedScalar (decodeScalar bytes) = 2 ^ 254 + 8 * (leValue bytes / 8 % 2 ^ 251) := by
  have h : decodeScalar bytes = fun i => (leValue bytes).testBit i :=
    funext (decodeScalar_eq_testBit bytes)
  rw [h, clampedScalar_testBit]

/-- **The clamped scalar is a multiple of 8.** -/
theorem clampedScalar_mod_eight (input : ℕ → Bool) : clampedScalar input % 8 = 0 := by
  rw [clampedScalar_eq]
  omega

/-- **The clamped scalar lies in `[2²⁵⁴, 2²⁵⁵)`.** -/
theorem clampedScalar_range (input : ℕ → Bool) :
    2 ^ 254 ≤ clampedScalar input ∧ clampedScalar input < 2 ^ 255 := by
  rw [clampedScalar_eq]
  have h := bitsValue_lt ((List.range 251).reverse.map (fun i => input (i + 3)))
  simp only [List.length_map, List.length_reverse, List.length_range] at h
  constructor
  · omega
  · have e : (2 : ℕ) ^ 255 = 2 ^ 254 + 8 * 2 ^ 251 := by norm_num
    rw [e]
    omega

end TlsMpcProofs.Ed25519
