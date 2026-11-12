import TlsMpc.MlKemFastKernels
import TlsMpc.EstablishProofs

/-!
Theorems about the fast KEM encapsulation (`TlsMpc/Signal/MlKemFast.lean`,
`TlsMpc/MlKemFastKernels.lean`).

PROVED (standard axioms only; no `sorry`, no `native_decide`, no `bv_decide`):

* `compiled_correct`: for every kernel `find` returns, each exported gate-level
  output bit equals the corresponding bit of the kernel's Lean definition
  evaluated on the inputs.
* `kemHash_spec`, `kemNtt_spec`, `kemMatrix_spec`, `kemU_spec`, `kemV_spec`,
  `kemFinish_spec`, `kemSample_spec`: on every input assignment, the kernel's
  output fields are the stage function of `MlKemFast` on VALUES (12-bit words),
  applied to the values of the kernel's input fields.
* The arithmetic on values, for every input in range:
  `addValue_toNat`, `subValue_toNat` (inputs below q), `mulValue_toNat` (any
  two 12-bit words), `mulConstValue_toNat` (any constant below q, any 12-bit
  word), `compress11_toNat`, `compress5_toNat`, `ltQValue_eq`,
  `cbd_coefficient`: each is the natural-number formula of FIPS 203.
* Refinement to the existing specification (`Signal.MlKemNtt`,
  `Signal.MlKemPke`, `Signal.MlKemEncoding` on 32-bit words): on polynomials
  whose coefficients are below q, `forward`, `inverse`, `baseMultiply`, `add`
  and `dot` give, coefficient for coefficient, the specification's result
  (`forward_refines`, `inverse_refines`, `baseMultiply_refines`, `add_refines`,
  `dot_refines`), and stay below q; `compress_refines` for 11 and 5 bits.
* `finish_rejects`: if any check byte is not 255, the status is 0 and the
  ciphertext and the secret are all zero. `finish_accepts`: otherwise the
  status is 255 and they pass unchanged.
* `sample_small`: the compaction network returns the first three accepted of
  six candidates, or zeros, on all 64 acceptance patterns (a kernel
  computation; the size the kernels use is NOT covered, see below).

Proved elsewhere since (2026-11-12): the compaction network at the size used
(`TlsMpc/KernelSpecs/KemSample.lean`: `compact_spec`, `sample_eq`), the
bit-list encodings (`KemEncoding.lean`: `decode12_refines`, `encode_refines`,
`cbd_refines`, `messagePoly_refines`), and the composition: the six stages,
wired by name as the worker wires them, equal `Signal.MlKem.encapsulate` on a
valid key and are zero on an invalid one (`KemCompose.lean`:
`kernels_compose`, `pipeline_valid_accept`, `pipeline_valid_reject`,
`pipeline_invalid`; `TlsMpc/Security.lean` section 2e). Still only tested
(`handshake_backend/EmpHybridWork/check_kem_kernels.py`,
`scripts/check_lean_signal_mlkem.py`): that the specification equals libcrux.

Nothing here is a security statement.
-/
namespace TlsMpc.Signal.MlKemFast
open Std.Tactic.BVDecide

/-! ### Arithmetic on values -/

theorem toNat_zx (k : Nat) (x : BitVec w) : (0#k ++ x).toNat = x.toNat := by
  simp [BitVec.toNat_append]

set_option maxRecDepth 1000000 in
theorem condSub_spec : ∀ s : BitVec 13, s.toNat < 6658 → (condSub s).toNat = s.toNat % 3329 := by
  decide +kernel

theorem sub13_toNat (x y : BitVec 13) : (sub13 x y).toNat = (8192 + x.toNat - y.toNat) % 8192 := by
  have hx := x.isLt
  have hy := y.isLt
  simp only [sub13, BitVec.toNat_not, BitVec.toNat_add]
  omega

theorem addValue_toNat (x y : BitVec 12) (hx : x.toNat < 3329) (hy : y.toNat < 3329) :
    (addValue x y).toNat = (x.toNat + y.toNat) % 3329 := by
  have sum : ((0#1 ++ x) + (0#1 ++ y) : BitVec 13).toNat = x.toNat + y.toNat := by
    rw [BitVec.toNat_add, toNat_zx, toNat_zx]
    omega
  rw [addValue, condSub_spec _ (by rw [sum]; omega), sum]

theorem addValue_lt (x y : BitVec 12) (hx : x.toNat < 3329) (hy : y.toNat < 3329) :
    (addValue x y).toNat < 3329 := by
  rw [addValue_toNat x y hx hy]
  exact Nat.mod_lt _ (by decide)

set_option maxRecDepth 1000000 in
theorem subFix_spec : ∀ d : BitVec 13,
    (d.toNat < 3329 →
      (d.extractLsb' 0 12 + (3329#12 &&& BitVec.replicate 12 (d.extractLsb' 12 1))).toNat = d.toNat) ∧
    (4864 ≤ d.toNat →
      (d.extractLsb' 0 12 + (3329#12 &&& BitVec.replicate 12 (d.extractLsb' 12 1))).toNat = d.toNat - 4863) := by
  decide +kernel

theorem subValue_toNat (x y : BitVec 12) (hx : x.toNat < 3329) (hy : y.toNat < 3329) :
    (subValue x y).toNat = (3329 + x.toNat - y.toNat) % 3329 := by
  have difference : (sub13 (0#1 ++ x) (0#1 ++ y)).toNat = (8192 + x.toNat - y.toNat) % 8192 := by
    rw [sub13_toNat, toNat_zx, toNat_zx]
  have fix := subFix_spec (sub13 (0#1 ++ x) (0#1 ++ y))
  rw [difference] at fix
  show (BitVec.extractLsb' 0 12 (sub13 (0#1 ++ x) (0#1 ++ y)) +
    (3329#12 &&& BitVec.replicate 12 (BitVec.extractLsb' 12 1 (sub13 (0#1 ++ x) (0#1 ++ y))))).toNat = _
  by_cases order : y.toNat ≤ x.toNat
  · rw [fix.1 (by omega)]
    omega
  · rw [fix.2 (by omega)]
    omega

theorem subValue_lt (x y : BitVec 12) (hx : x.toNat < 3329) (hy : y.toNat < 3329) :
    (subValue x y).toNat < 3329 := by
  rw [subValue_toNat x y hx hy]
  exact Nat.mod_lt _ (by decide)

/-! The multiplier: its rows are the standard library's `BitVec.mulRec`. -/

theorem bit_cases (b : BitVec 1) : (b = 0#1 ∧ b.getLsbD 0 = false) ∨ (b = 1#1 ∧ b.getLsbD 0 = true) := by
  rcases BitVec.eq_zero_or_eq_one b with h | h <;> subst h <;> simp

theorem row_eq (x y : BitVec 12) (n : Nat) (h : n < 12) :
    (((0#12 ++ x) <<< BitVec.ofNat 5 n) &&& BitVec.replicate 24 (y.extractLsb' n 1) : BitVec 24) =
      if (0#12 ++ y : BitVec 24).getLsbD n = true then (0#12 ++ x : BitVec 24) <<< n else 0 := by
  have shift : ((0#12 ++ x : BitVec 24) <<< BitVec.ofNat 5 n) = (0#12 ++ x : BitVec 24) <<< n := by
    rw [BitVec.shiftLeft_eq', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have bit : (0#12 ++ y : BitVec 24).getLsbD n = (y.extractLsb' n 1).getLsbD 0 := by
    have left : (0#12 ++ y : BitVec 24).getLsbD n = y.getLsbD n := by
      simp only [BitVec.getLsbD, toNat_zx]
    rw [left]
    simp [h]
  have zero : BitVec.replicate 24 0#1 = 0#24 := by decide
  have ones : BitVec.replicate 24 1#1 = BitVec.allOnes 24 := by decide
  rw [shift, bit]
  rcases BitVec.eq_zero_or_eq_one (y.extractLsb' n 1) with value | value
  · rw [value, zero, BitVec.and_zero, if_neg (by decide)]
    exact rfl
  · rw [value, ones, BitVec.and_allOnes, if_pos (by decide)]

theorem mulRows_eq (x y : BitVec 12) : ∀ n, n < 12 →
    mulRows x y (n + 1) = BitVec.mulRec (0#12 ++ x : BitVec 24) (0#12 ++ y) n
  | 0, _ => by
      rw [mulRows, mulRows, BitVec.mulRec_zero_eq, row_eq x y 0 (by decide)]
      simp
  | n + 1, h => by
      rw [mulRows, mulRows_eq x y n (by omega), BitVec.mulRec_succ_eq, row_eq x y (n + 1) h]

theorem mulRows_toNat (x y : BitVec 12) : (mulRows x y 12).toNat = x.toNat * y.toNat := by
  have hx := x.isLt
  have hy := y.isLt
  have narrow : BitVec.setWidth 24 (BitVec.setWidth 12 (0#12 ++ y : BitVec 24)) = (0#12 ++ y : BitVec 24) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, toNat_zx]
    omega
  have product : x.toNat * y.toNat < 4096 * 4096 := Nat.mul_lt_mul'' hx hy
  rw [mulRows_eq x y 11 (by decide), BitVec.mulRec_eq_mul_signExtend_setWidth, narrow, BitVec.toNat_mul,
    toNat_zx, toNat_zx]
  omega

theorem barrett_nat (v : Nat) (hv : v < 16777216) :
    (v / 512 * 5039 / 32768) * 3329 ≤ v ∧ v - (v / 512 * 5039 / 32768) * 3329 < 6658 := by omega

theorem reduce24_toNat (v : BitVec 24) : (reduce24 v).toNat = v.toNat % 3329 := by
  have hv : v.toNat < 16777216 := v.isLt
  have high : (v.extractLsb' 9 15).toNat = v.toNat / 512 := by
    rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    omega
  have estimate : ((0#13 ++ v.extractLsb' 9 15 : BitVec 28) * 5039#28).toNat = v.toNat / 512 * 5039 := by
    rw [BitVec.toNat_mul, toNat_zx, high]
    simp only [BitVec.toNat_ofNat]
    omega
  have quotient : (((0#13 ++ v.extractLsb' 9 15 : BitVec 28) * 5039#28).extractLsb' 15 13).toNat =
      v.toNat / 512 * 5039 / 32768 := by
    rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, estimate]
    omega
  have low : (v.extractLsb' 0 13).toNat = v.toNat % 8192 := by
    rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    omega
  have bounds := barrett_nat v.toNat hv
  have remainder : (sub13 (v.extractLsb' 0 13)
      ((((0#13 ++ v.extractLsb' 9 15 : BitVec 28) * 5039#28).extractLsb' 15 13) * 3329#13)).toNat =
      v.toNat - (v.toNat / 512 * 5039 / 32768) * 3329 := by
    rw [sub13_toNat, BitVec.toNat_mul, quotient, low]
    simp only [BitVec.toNat_ofNat]
    omega
  show (condSub _).toNat = _
  rw [condSub_spec _ (by rw [remainder]; exact bounds.2), remainder]
  omega

theorem mulValue_toNat (x y : BitVec 12) : (mulValue x y).toNat = (x.toNat * y.toNat) % 3329 := by
  rw [mulValue, reduce24_toNat, mulRows_toNat]

theorem mulValue_lt (x y : BitVec 12) : (mulValue x y).toNat < 3329 := by
  rw [mulValue_toNat]
  exact Nat.mod_lt _ (by decide)

theorem shoup_nat (x c : Nat) (hx : x < 4096) :
    (x * (c * 4096 / 3329) / 4096) * 3329 ≤ x * c ∧ x * c - (x * (c * 4096 / 3329) / 4096) * 3329 < 6658 := by
  have split := Nat.div_add_mod (c * 4096) 3329
  have small := Nat.mod_lt (c * 4096) (show 0 < 3329 by decide)
  generalize c * 4096 / 3329 = c' at split ⊢
  generalize c * 4096 % 3329 = rho at split small
  have key : x * c * 4096 = x * c' * 3329 + x * rho := by
    rw [Nat.mul_assoc, ← split, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm 3329 c']
  have bound : x * rho ≤ 4095 * 3328 := Nat.mul_le_mul (by omega) (by omega)
  generalize x * c = A at key ⊢
  generalize x * c' = B at key ⊢
  generalize x * rho = E at key bound
  omega

theorem mulConstValue_toNat (c : Nat) (x : BitVec 12) (hc : c < 3329) :
    (mulConstValue c x).toNat = (x.toNat * c) % 3329 := by
  have hx : x.toNat < 4096 := x.isLt
  have scaled : c * 4096 / 3329 < 4096 := by omega
  have bounds := shoup_nat x.toNat c hx
  have wide : x.toNat * (c * 4096 / 3329) < 4096 * 4096 := Nat.mul_lt_mul'' hx scaled
  simp only [mulConstValue]
  generalize c * 4096 / 3329 = c' at scaled bounds wide ⊢
  have product : ((0#12 ++ x : BitVec 24) * BitVec.ofNat 24 c').toNat = x.toNat * c' := by
    rw [BitVec.toNat_mul, toNat_zx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c' < 2 ^ 24 by omega)]
    omega
  have quotient : (0#1 ++ ((0#12 ++ x : BitVec 24) * BitVec.ofNat 24 c').extractLsb' 12 12 : BitVec 13).toNat =
      x.toNat * c' / 4096 := by
    rw [toNat_zx, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, product]
    omega
  have low : ((0#1 ++ x : BitVec 13) * BitVec.ofNat 13 c).toNat = (x.toNat * c) % 8192 := by
    rw [BitVec.toNat_mul, toNat_zx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c < 2 ^ 13 by omega)]
  have remainder : (sub13 ((0#1 ++ x : BitVec 13) * BitVec.ofNat 13 c)
      ((0#1 ++ ((0#12 ++ x : BitVec 24) * BitVec.ofNat 24 c').extractLsb' 12 12 : BitVec 13) * 3329#13)).toNat =
      x.toNat * c - (x.toNat * c' / 4096) * 3329 := by
    rw [sub13_toNat, low, BitVec.toNat_mul, quotient]
    simp only [BitVec.toNat_ofNat]
    generalize x.toNat * c = A at bounds ⊢
    generalize x.toNat * c' / 4096 = q at bounds ⊢
    omega
  rw [condSub_spec _ (by rw [remainder]; exact bounds.2), remainder]
  generalize x.toNat * c = A at bounds ⊢
  generalize x.toNat * c' / 4096 = q at bounds ⊢
  omega

theorem mulConstValue_lt (c : Nat) (x : BitVec 12) (hc : c < 3329) : (mulConstValue c x).toNat < 3329 := by
  rw [mulConstValue_toNat c x hc]
  exact Nat.mod_lt _ (by decide)

set_option maxRecDepth 1000000 in
theorem compress11_toNat : ∀ x : BitVec 12, x.toNat < 3329 →
    (compressValue 11 x).toNat = ((x.toNat * 2 ^ 11 + 1664) / 3329) % 2 ^ 11 := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem compress5_toNat : ∀ x : BitVec 12, x.toNat < 3329 →
    (compressValue 5 x).toNat = ((x.toNat * 2 ^ 5 + 1664) / 3329) % 2 ^ 5 := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem ltQValue_eq : ∀ x : BitVec 12, ltQValue x = if x.toNat < 3329 then 1#1 else 0#1 := by
  decide +kernel

/-- One coefficient of the centered binomial sample: `(b0 + b1) - (b2 + b3)` modulo q. -/
theorem cbd_coefficient : ∀ b0 b1 b2 b3 : BitVec 1,
    (subValue (concrete.ofBits [b0 ^^^ b1, b0 &&& b1]) (concrete.ofBits [b2 ^^^ b3, b2 &&& b3])).toNat =
      (3329 + (b0.toNat + b1.toNat) - (b2.toNat + b3.toNat)) % 3329 := by
  decide +kernel

/-! ### Refinement to the specification on 32-bit words -/

/-- A 12-bit coefficient as the specification's 32-bit word. -/
def wide (x : BitVec 12) : BitVec 32 := x.setWidth 32

theorem wide_toNat (x : BitVec 12) : (wide x).toNat = x.toNat := by
  have := x.isLt
  simp only [wide, BitVec.toNat_setWidth]
  omega

/-- Every coefficient is below q. -/
def Canon (p : List (BitVec 12)) : Prop := ∀ x ∈ p, x.toNat < 3329

abbrev specR := MlKemArithmetic.concrete
abbrev specS := Sha256.concrete

theorem const_toNat (c : Nat) (hc : c < 3329) : (specS.wordConst c).toNat = c := by
  show (BitVec.ofNat 32 c).toNat = c
  rw [BitVec.toNat_ofNat]
  omega

theorem add_lt (x y : BitVec 12) (hx : x.toNat < 3329) (hy : y.toNat < 3329) :
    (concrete.addMod x y).toNat < 3329 := addValue_lt x y hx hy
theorem sub_lt (x y : BitVec 12) (hx : x.toNat < 3329) (hy : y.toNat < 3329) :
    (concrete.subMod x y).toNat < 3329 := subValue_lt x y hx hy
theorem mul_lt (x y : BitVec 12) : (concrete.mulMod x y).toNat < 3329 := mulValue_lt x y
theorem mulConst_lt (c : Nat) (x : BitVec 12) (hc : c < 3329) : (concrete.mulConst c x).toNat < 3329 :=
  mulConstValue_lt c x hc

theorem wide_add (x y : BitVec 12) (hx : x.toNat < 3329) (hy : y.toNat < 3329) :
    wide (concrete.addMod x y) = MlKemArithmetic.addMod specR specS (wide x) (wide y) := by
  apply BitVec.eq_of_toNat_eq
  rw [MlKemArithmetic.addMod_value _ _ (by rw [wide_toNat]; exact hx) (by rw [wide_toNat]; exact hy),
    wide_toNat, wide_toNat, wide_toNat]
  exact addValue_toNat x y hx hy

theorem wide_sub (x y : BitVec 12) (hx : x.toNat < 3329) (hy : y.toNat < 3329) :
    wide (concrete.subMod x y) = MlKemArithmetic.subMod specR specS (wide x) (wide y) := by
  apply BitVec.eq_of_toNat_eq
  rw [MlKemArithmetic.subMod_value _ _ (by rw [wide_toNat]; exact hx) (by rw [wide_toNat]; exact hy),
    wide_toNat, wide_toNat, wide_toNat]
  exact subValue_toNat x y hx hy

theorem wide_mul (x y : BitVec 12) (hx : x.toNat < 3329) (hy : y.toNat < 3329) :
    wide (concrete.mulMod x y) = MlKemArithmetic.mulMod specR (wide x) (wide y) := by
  apply BitVec.eq_of_toNat_eq
  rw [MlKemArithmetic.mulMod_value _ _ (by rw [wide_toNat]; exact hx) (by rw [wide_toNat]; exact hy),
    wide_toNat, wide_toNat, wide_toNat]
  exact mulValue_toNat x y

theorem wide_mulConst (c : Nat) (x : BitVec 12) (hc : c < 3329) (hx : x.toNat < 3329) :
    wide (concrete.mulConst c x) = MlKemArithmetic.mulMod specR (specS.wordConst c) (wide x) := by
  apply BitVec.eq_of_toNat_eq
  rw [MlKemArithmetic.mulMod_value _ _ (by rw [const_toNat c hc]; exact hc) (by rw [wide_toNat]; exact hx),
    wide_toNat, wide_toNat, const_toNat c hc, Nat.mul_comm]
  exact mulConstValue_toNat c x hc

theorem wide_mulConst_right (c : Nat) (x : BitVec 12) (hc : c < 3329) (hx : x.toNat < 3329) :
    wide (concrete.mulConst c x) = MlKemArithmetic.mulMod specR (wide x) (specS.wordConst c) := by
  apply BitVec.eq_of_toNat_eq
  rw [MlKemArithmetic.mulMod_value _ _ (by rw [wide_toNat]; exact hx) (by rw [const_toNat c hc]; exact hc),
    wide_toNat, wide_toNat, const_toNat c hc]
  exact mulConstValue_toNat c x hc

theorem wide_compress11 (x : BitVec 12) (hx : x.toNat < 3329) :
    wide (concrete.compress 11 x) =
      MlKemEncoding.compress specR MlKemEncoding.concrete specS 11 (wide x) := by
  apply BitVec.eq_of_toNat_eq
  rw [MlKemEncoding.compress_value 11 _ (by decide) (by rw [wide_toNat]; exact hx), wide_toNat, wide_toNat]
  exact compress11_toNat x hx

theorem wide_compress5 (x : BitVec 12) (hx : x.toNat < 3329) :
    wide (concrete.compress 5 x) =
      MlKemEncoding.compress specR MlKemEncoding.concrete specS 5 (wide x) := by
  apply BitVec.eq_of_toNat_eq
  rw [MlKemEncoding.compress_value 5 _ (by decide) (by rw [wide_toNat]; exact hx), wide_toNat, wide_toNat]
  exact compress5_toNat x hx

theorem wide_get (p : List (BitVec 12)) (i : Nat) :
    wide (get concrete p i) = MlKemNtt.get specS (p.map wide) i := by
  simp only [get, MlKemNtt.get, List.getElem?_map]
  cases p[i]? <;> rfl

theorem get_lt (p : List (BitVec 12)) (hp : Canon p) (i : Nat) : (get concrete p i).toNat < 3329 := by
  simp only [get]
  cases h : p[i]? with
  | none => exact (by decide : (BitVec.ofNat 12 0).toNat < 3329)
  | some x => exact hp x (List.mem_of_getElem? h)

theorem zeta_lt (i : Nat) : MlKemNtt.zeta i < 3329 := Nat.mod_lt _ (by decide)

theorem forwardLayer_refines (level : Nat) (p : List (BitVec 12)) (hp : Canon p) :
    (forwardLayer concrete level p).map wide = MlKemNtt.forwardLayer specR specS level (p.map wide) ∧
      Canon (forwardLayer concrete level p) := by
  constructor
  · simp only [forwardLayer, MlKemNtt.forwardLayer, List.map_map]
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply]
    by_cases c : i % (2 * (128 / 2 ^ level)) < 128 / 2 ^ level
    · simp only [c, ↓reduceIte]
      rw [wide_add _ _ (get_lt p hp _) (mulConst_lt _ _ (zeta_lt _)),
        wide_mulConst _ _ (zeta_lt _) (get_lt p hp _), wide_get, wide_get]
    · simp only [c, ↓reduceIte]
      rw [wide_sub _ _ (get_lt p hp _) (mulConst_lt _ _ (zeta_lt _)),
        wide_mulConst _ _ (zeta_lt _) (get_lt p hp _), wide_get, wide_get]
  · intro x hx
    simp only [forwardLayer, List.mem_map] at hx
    obtain ⟨i, _, rfl⟩ := hx
    split
    · exact add_lt _ _ (get_lt p hp _) (mulConst_lt _ _ (zeta_lt _))
    · exact sub_lt _ _ (get_lt p hp _) (mulConst_lt _ _ (zeta_lt _))

theorem inverseLayer_refines (level : Nat) (p : List (BitVec 12)) (hp : Canon p) :
    (inverseLayer concrete level p).map wide = MlKemNtt.inverseLayer specR specS level (p.map wide) ∧
      Canon (inverseLayer concrete level p) := by
  constructor
  · simp only [inverseLayer, MlKemNtt.inverseLayer, List.map_map]
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply]
    by_cases c : i % (2 * (2 * 2 ^ level)) < 2 * 2 ^ level
    · simp only [c, ↓reduceIte]
      rw [wide_add _ _ (get_lt p hp _) (get_lt p hp _), wide_get, wide_get]
    · simp only [c, ↓reduceIte]
      rw [wide_mulConst _ _ (zeta_lt _) (sub_lt _ _ (get_lt p hp _) (get_lt p hp _)),
        wide_sub _ _ (get_lt p hp _) (get_lt p hp _), wide_get, wide_get]
  · intro x hx
    simp only [inverseLayer, List.mem_map] at hx
    obtain ⟨i, _, rfl⟩ := hx
    split
    · exact add_lt _ _ (get_lt p hp _) (get_lt p hp _)
    · exact mulConst_lt _ _ (zeta_lt _)

theorem forwardLoop_refines (levels : List Nat) (p : List (BitVec 12)) (hp : Canon p) :
    (levels.foldl (fun state level => forwardLayer concrete level state) p).map wide =
        levels.foldl (fun state level => MlKemNtt.forwardLayer specR specS level state) (p.map wide) ∧
      Canon (levels.foldl (fun state level => forwardLayer concrete level state) p) := by
  induction levels generalizing p with
  | nil => exact ⟨rfl, hp⟩
  | cons level rest ih =>
      simp only [List.foldl_cons]
      rw [← (forwardLayer_refines level p hp).1]
      exact ih _ (forwardLayer_refines level p hp).2

theorem inverseLoop_refines (levels : List Nat) (p : List (BitVec 12)) (hp : Canon p) :
    (levels.foldl (fun state level => inverseLayer concrete level state) p).map wide =
        levels.foldl (fun state level => MlKemNtt.inverseLayer specR specS level state) (p.map wide) ∧
      Canon (levels.foldl (fun state level => inverseLayer concrete level state) p) := by
  induction levels generalizing p with
  | nil => exact ⟨rfl, hp⟩
  | cons level rest ih =>
      simp only [List.foldl_cons]
      rw [← (inverseLayer_refines level p hp).1]
      exact ih _ (inverseLayer_refines level p hp).2

/-- The NTT of a polynomial with coefficients below q is the specification's, and stays below q. -/
theorem forward_refines (p : List (BitVec 12)) (hp : Canon p) :
    (forward concrete p).map wide = MlKemNtt.forward specR specS (p.map wide) ∧ Canon (forward concrete p) :=
  forwardLoop_refines _ p hp

/-- The same for the inverse NTT. -/
theorem inverse_refines (p : List (BitVec 12)) (hp : Canon p) :
    (inverse concrete p).map wide = MlKemNtt.inverse specR specS (p.map wide) ∧ Canon (inverse concrete p) := by
  obtain ⟨loop, canon⟩ := inverseLoop_refines (List.range 7) p hp
  constructor
  · simp only [inverse, MlKemNtt.inverse]
    rw [← loop, List.map_map, List.map_map]
    apply List.map_congr_left
    intro x hx
    exact wide_mulConst_right 3303 x (by decide) (canon x hx)
  · intro x hx
    simp only [inverse, List.mem_map] at hx
    obtain ⟨y, _, rfl⟩ := hx
    exact mulConst_lt _ _ (by decide)

/-- Multiplication in the NTT domain. -/
theorem baseMultiply_refines (l r : List (BitVec 12)) (hl : Canon l) (hr : Canon r) :
    (baseMultiply concrete l r).map wide = MlKemNtt.baseMultiply specR specS (l.map wide) (r.map wide) ∧
      Canon (baseMultiply concrete l r) := by
  have gamma (i : Nat) : 17 ^ (2 * MlKemNtt.reverseBits 7 i + 1) % 3329 < 3329 := Nat.mod_lt _ (by decide)
  constructor
  · simp only [baseMultiply, MlKemNtt.baseMultiply, List.map_map]
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply]
    by_cases c : i % 2 = 0
    · simp only [c, ↓reduceIte]
      rw [wide_add _ _ (mul_lt _ _) (mulConst_lt _ _ (gamma _)),
        wide_mul _ _ (get_lt l hl _) (get_lt r hr _),
        wide_mulConst _ _ (gamma _) (mul_lt _ _),
        wide_mul _ _ (get_lt l hl _) (get_lt r hr _), wide_get, wide_get, wide_get, wide_get]
    · simp only [c, ↓reduceIte]
      rw [wide_add _ _ (mul_lt _ _) (mul_lt _ _),
        wide_mul _ _ (get_lt l hl _) (get_lt r hr _),
        wide_mul _ _ (get_lt l hl _) (get_lt r hr _), wide_get, wide_get, wide_get, wide_get]
  · intro x hx
    simp only [baseMultiply, List.mem_map] at hx
    obtain ⟨i, _, rfl⟩ := hx
    split
    · exact add_lt _ _ (mul_lt _ _) (mulConst_lt _ _ (gamma _))
    · exact add_lt _ _ (mul_lt _ _) (mul_lt _ _)

/-- Coefficient-wise addition. -/
theorem add_refines (x y : List (BitVec 12)) (hx : Canon x) (hy : Canon y) :
    (add concrete x y).map wide = MlKemPke.add specR specS (x.map wide) (y.map wide) ∧
      Canon (add concrete x y) := by
  induction x generalizing y with
  | nil => exact ⟨rfl, fun _ h => nomatch h⟩
  | cons a as ih =>
      cases y with
      | nil => exact ⟨rfl, fun _ h => nomatch h⟩
      | cons b bs =>
          have ha := hx a (List.mem_cons.mpr (Or.inl rfl))
          have hb := hy b (List.mem_cons.mpr (Or.inl rfl))
          have rest := ih bs (fun z hz => hx z (List.mem_cons.mpr (Or.inr hz)))
            (fun z hz => hy z (List.mem_cons.mpr (Or.inr hz)))
          constructor
          · show wide (concrete.addMod a b) :: (add concrete as bs).map wide =
              MlKemArithmetic.addMod specR specS (wide a) (wide b) :: MlKemPke.add specR specS (as.map wide) (bs.map wide)
            rw [wide_add a b ha hb, rest.1]
          · intro z hz
            have split : z = concrete.addMod a b ∨ z ∈ add concrete as bs := List.mem_cons.mp hz
            rcases split with rfl | inside
            · exact add_lt a b ha hb
            · exact rest.2 z inside

theorem sumLoop_refines (polys : List (List (BitVec 12))) (acc : List (BitVec 12)) (hacc : Canon acc)
    (hp : ∀ q ∈ polys, Canon q) :
    (polys.foldl (add concrete) acc).map wide =
        (polys.map (List.map wide)).foldl (MlKemPke.add specR specS) (acc.map wide) ∧
      Canon (polys.foldl (add concrete) acc) := by
  induction polys generalizing acc with
  | nil => exact ⟨rfl, hacc⟩
  | cons q rest ih =>
      have hq := hp q (List.mem_cons.mpr (Or.inl rfl))
      have step := add_refines acc q hacc hq
      simp only [List.foldl_cons, List.map_cons]
      rw [← step.1]
      exact ih _ step.2 (fun z hz => hp z (List.mem_cons.mpr (Or.inr hz)))

/-- The inner product of two vectors of polynomials in the NTT domain. -/
theorem dot_refines (rank : Nat) (left right : Nat → List (BitVec 12))
    (hl : ∀ i, Canon (left i)) (hr : ∀ i, Canon (right i)) :
    (dot concrete rank left right).map wide =
        MlKemPke.dot specR specS rank (fun i => (left i).map wide) (fun i => (right i).map wide) ∧
      Canon (dot concrete rank left right) := by
  have zero : Canon (zeroPoly concrete) := by
    intro x hx
    rw [List.eq_of_mem_replicate hx]
    exact (by decide : (BitVec.ofNat 12 0).toNat < 3329)
  have products : ∀ q ∈ (List.range rank).map (fun i => baseMultiply concrete (left i) (right i)), Canon q := by
    intro q hq
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hq
    exact (baseMultiply_refines _ _ (hl i) (hr i)).2
  obtain ⟨value, canon⟩ := sumLoop_refines _ (zeroPoly concrete) zero products
  refine ⟨?_, canon⟩
  simp only [dot, sum, MlKemPke.dot, MlKemPke.sum]
  rw [value, List.map_map]
  have start : (zeroPoly concrete).map wide = MlKemPke.zero specS := by
    simp only [zeroPoly, MlKemPke.zero, List.map_replicate]
    rfl
  have each : (List.range rank).map (List.map wide ∘ fun i => baseMultiply concrete (left i) (right i)) =
      (List.range rank).map (fun i => MlKemNtt.baseMultiply specR specS ((left i).map wide) ((right i).map wide)) := by
    apply List.map_congr_left
    intro i _
    exact (baseMultiply_refines _ _ (hl i) (hr i)).1
  rw [start, each]

/-! ### The compaction network, exhaustively at a small size

The general statement (any number of candidates) is not proved. This is the same network
definition, run on every acceptance pattern of six candidates. -/

/-- What the sampler must return: the first `count` candidates below q, or zeros. -/
def firstAccepted (count : Nat) (candidates : List (BitVec 12)) : BitVec 1 × List (BitVec 12) :=
  let accepted := candidates.filter (fun c => c.toNat < 3329)
  if count ≤ accepted.length then (1#1, accepted.take count) else (0#1, List.replicate count 0)

/-- Candidate `k` is `k + 1` when bit `k` of the pattern is set and `3329 + k` (rejected) otherwise. -/
def pattern (m : Nat) : List (BitVec 12) :=
  (List.range 6).map (fun k => if m.testBit k then BitVec.ofNat 12 (k + 1) else BitVec.ofNat 12 (3329 + k))

set_option maxRecDepth 1000000 in
theorem sample_small : ∀ m : Fin 64, sample concrete 3 (pattern m.val) = firstAccepted 3 (pattern m.val) := by
  decide +kernel

/-! ### Acceptance and rejection -/

theorem release_zero (bytes : List (BitVec 8)) : ∀ b ∈ ByteAuth.release ByteAuth.concrete 0 bytes, b = 0 := by
  intro b hb
  simp only [ByteAuth.release, List.mem_map] at hb
  obtain ⟨x, _, rfl⟩ := hb
  exact BitVec.zero_and

/-- If any check byte is not 255, the status is 0 and nothing else is released. -/
theorem finish_rejects (kyber : Bool) (ciphertext kbar checks : List (BitVec 8))
    (failed : checks.foldl ByteAuth.concrete.and (ByteAuth.concrete.const 255) ≠ ByteAuth.concrete.const 255) :
    ∀ field ∈ finishStage ByteAuth.concrete Keccak.concrete kyber ciphertext kbar checks,
      ∀ byte ∈ field, byte = 0 := by
  intro field member byte inside
  simp only [finishStage, ByteAuth.eqMask_value, if_neg failed, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · simpa using inside
  · exact release_zero _ _ inside
  · exact release_zero _ _ inside

/-- If every check byte is 255, the status is 255 and the ciphertext and secret pass unchanged. -/
theorem finish_accepts (kyber : Bool) (ciphertext kbar checks : List (BitVec 8))
    (passed : checks.foldl ByteAuth.concrete.and (ByteAuth.concrete.const 255) = ByteAuth.concrete.const 255) :
    finishStage ByteAuth.concrete Keccak.concrete kyber ciphertext kbar checks =
      [[255], ciphertext,
        if kyber then Keccak.shake256 Keccak.concrete 32 (kbar ++ Keccak.sha3_256 Keccak.concrete ciphertext) else kbar] := by
  simp only [finishStage, ByteAuth.eqMask_value, if_pos passed, ByteAuth.release_accept]

#print axioms addValue_toNat
#print axioms subValue_toNat
#print axioms mulValue_toNat
#print axioms mulConstValue_toNat
#print axioms compress11_toNat
#print axioms compress5_toNat
#print axioms ltQValue_eq
#print axioms cbd_coefficient
#print axioms forward_refines
#print axioms inverse_refines
#print axioms baseMultiply_refines
#print axioms dot_refines
#print axioms add_refines
#print axioms wide_compress11
#print axioms wide_compress5
#print axioms finish_rejects
#print axioms finish_accepts
#print axioms sample_small

end TlsMpc.Signal.MlKemFast

namespace TlsMpc.MlKemFastKernel
open Std.Tactic.BVDecide
open Signal
open HybridKernel (Kernel lookup)
open EstablishKernel (Kernel.values getD_map)

theorem compiled_correct (arguments : List String) (k : Kernel) (_found : find arguments = some k)
    (assign : BVExpr.Assignment) (index : Nat) (hi : index < 8 * k.bytes.length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr k.bytes)).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr k.bytes)).vec.get index hi)) =
    (ByteCircuit.joinValue (k.bytes.map (BVExpr.eval assign))).getLsbD index :=
  HybridKernel.compiled_correct k assign index hi

theorem kemHash_spec (kyber : Bool) (assign : BVExpr.Assignment) :
    let value := fun name => (lookup hashInputs name).map (BVExpr.eval assign)
    Kernel.values (kemHash kyber) assign =
      MlKemFast.hashStage MlKemFast.concrete ByteAuth.concrete Keccak.concrete kyber
        (value "kyberPrekey") (value "entropyA") (value "entropyB") := by
  intro value
  simp only [value, ← MlKemFast.hashStage_map (MlKemFast.evaluationHom assign) (ByteAuth.evaluationHom assign)
    (Keccak.evaluationHom assign)]
  rfl

theorem kemNtt_spec (assign : BVExpr.Assignment) :
    Kernel.values (kemNtt ()) assign =
      [MlKemFast.nttStage MlKemFast.concrete ByteAuth.concrete Keccak.concrete
        ((lookup nttInputs "coins").map (BVExpr.eval assign))] := by
  simp only [Kernel.values, kemNtt, HybridKernel.priv, List.map_cons, List.map_nil,
    MlKemFast.nttStage_map (MlKemFast.evaluationHom assign) (ByteAuth.evaluationHom assign)
    (Keccak.evaluationHom assign)]

theorem kemMatrix_spec (row : Nat) (assign : BVExpr.Assignment) :
    Kernel.values (kemMatrix row) assign =
      MlKemFast.matrixStage MlKemFast.concrete ByteAuth.concrete Keccak.concrete row
        ((lookup matrixInputs "kyberPrekey").map (BVExpr.eval assign)) := by
  simp only [← MlKemFast.matrixStage_map (MlKemFast.evaluationHom assign) (ByteAuth.evaluationHom assign)
    (Keccak.evaluationHom assign)]
  rfl

theorem kemU_spec (row : Nat) (assign : BVExpr.Assignment) :
    let value := fun name => (lookup (uInputs row) name).map (BVExpr.eval assign)
    Kernel.values (kemU row) assign =
      [MlKemFast.uStage MlKemFast.concrete ByteAuth.concrete Keccak.concrete row
        (value s!"row{row}") (value "rhat") (value "coins")] := by
  intro value
  simp only [value, ← MlKemFast.uStage_map (MlKemFast.evaluationHom assign) (ByteAuth.evaluationHom assign)
    (Keccak.evaluationHom assign)]
  rfl

theorem kemV_spec (assign : BVExpr.Assignment) :
    let value := fun name => (lookup vInputs name).map (BVExpr.eval assign)
    Kernel.values (kemV ()) assign =
      [MlKemFast.vStage MlKemFast.concrete ByteAuth.concrete Keccak.concrete
        (value "kyberPrekey") (value "rhat") (value "coins") (value "message")] := by
  intro value
  simp only [value, Kernel.values, kemV, HybridKernel.priv, List.map_cons, List.map_nil,
    MlKemFast.vStage_map (MlKemFast.evaluationHom assign) (ByteAuth.evaluationHom assign)
    (Keccak.evaluationHom assign)]

theorem kemFinish_spec (kyber : Bool) (assign : BVExpr.Assignment) :
    let get := lookup finishInputs
    let e := BVExpr.eval assign
    Kernel.values (kemFinish kyber) assign =
      MlKemFast.finishStage ByteAuth.concrete Keccak.concrete kyber
        ((get "u0" ++ get "u1" ++ get "u2" ++ get "u3" ++ get "v").map e) ((get "kbar").map e)
        ((get "ok0" ++ get "ok1" ++ get "ok2" ++ get "ok3" ++ get "keyValid").map e) := by
  intro get e
  simp only [e, ← MlKemFast.finishStage_map (ByteAuth.evaluationHom assign) (Keccak.evaluationHom assign)]
  rfl

theorem kemSample_spec (assign : BVExpr.Assignment) :
    Kernel.values (kemSample ()) assign =
      MlKemFast.sampleStage MlKemFast.concrete ((lookup sampleInputs "stream").map (BVExpr.eval assign)) := by
  simp only [Kernel.values, kemSample, HybridKernel.priv, List.map_cons, List.map_nil, getD_map,
    MlKemFast.sampleStage_map (MlKemFast.evaluationHom assign)]
  simp only [MlKemFast.sampleStage, List.getD_cons_zero, List.getD_cons_succ]

#print axioms compiled_correct
#print axioms kemHash_spec
#print axioms kemNtt_spec
#print axioms kemMatrix_spec
#print axioms kemU_spec
#print axioms kemV_spec
#print axioms kemFinish_spec
#print axioms kemSample_spec

end TlsMpc.MlKemFastKernel
