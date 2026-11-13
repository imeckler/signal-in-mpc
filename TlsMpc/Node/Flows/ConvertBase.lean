import TlsMpc.Node.Flows.ContactsBase
import TlsMpc.WordMask
import TlsMpc.FieldBits
import TlsMpc.X25519SwapBits
import TlsMpc.FieldProgramsV3

/-!
# Conversions and masks: words, word circuits, field programs, the mask pool (stage S10)

REORGANIZATION_PLAN.md 7.1 (P-CUT, P-PAIR, P-B2F, P-W2F, P-F2W, P-BITS, P-INV), stage S10. The
definitions the S10 flows share (`Flows/Masks.lean`, `Flows/Convert.lean`, `Flows/Inversion.lean`,
`Account.openStep`). No I/O; no emitter imports this module (it imports `WordMask`,
`FieldBits`, `X25519SwapBits`, `FieldProgramsV3`, which the emitters also import, and changes
none of them).

WHAT IS HERE.
  * Words: `natOf` (a bit list's value, least significant bit first, `WordMask.val`'s order) and
    `bitsOfNat` (the low bits of a number), with their round trips.
  * The word circuits as the model sees them (`Engine.Circuit`): exact arithmetic specifications
    of `TlsMpc/WordMask.lean`'s exported circuits on EVERY input (canonical or not: the cheating
    cases need the non-canonical behaviour). `addModSpec x y` is the value of `modAdd` (`condSub`
    of the 256-bit sum): `x + y − p` when `x + y ≥ p`, else `x + y`, truncated to 255 bits.
    `modAdd_exact`, `reduceOnce_exact`, `finalize*_exact`, `intoField_exact`: the Lean circuits
    (`BoolDag.Expr` lists) compute exactly these, for every assignment. So `WordLoaded E` (the
    environment's word circuits are these specifications) is the T2 trust in the pinned flat files
    (they compute the Lean circuits), and nothing else.
  * The circuit NAMES a script runs and their open MARKS (the Rust loader's `WORD_CIRCUITS` table
    fixes the same marks): the same pinned file can be registered under two names with different
    marks, `modadd` (output never: field to word) and `modadd-open` (output public: the bucket
    check), `xor-bit` (never) and `xor-bit-open` (public: bits to field), `into-field-open`
    (public: word to field), `finalize-mask` / `finalize-bits` (255 never, then the public flag),
    `swap-bits` (252 never).
  * The field programs a script names: `field-bit-check`, `field-bit-xor`, `field-recompose` (the
    exported V3 programs of `FieldProgramsV3`) and one natively written V3 program of S10,
    `field-mask-sub` (inputs `v`, `f`; output `v − f`, public): field to word must open `v − f`,
    which the open rule refuses for `fieldSub` (the join of `never` with anything is `never`);
    a program's outputs carry the marks its pinned file declares (decision D14), so the opening
    is declared there. `ProgsLoaded E`: the environment's programs under those names compute the
    stated values without masks; `computes_of_decl` discharges it for an exported program from its
    declaration and `p.masks = 0` (with `FieldInverse`).
  * The mask pool (`MaskPool`): word masks (a 255-bit word handle and a field handle) and bit
    pairs (a bit of a Boolean bundle and a field handle). `takeWord` / `takeBits` hand out the
    first entries and return the pool without them: P-CUT (h), single use, is `take*_fresh` and
    `takes_distinct` (no entry is handed out twice).
-/

namespace TlsMpc.Node.Flows.Conv

open TlsMpc.Node.Engine
open TlsMpc.FieldDag (F modulus)

/-! ## Words -/

/-- The value of a bit list, least significant bit first (`WordMask.val` on constants). -/
def natOf : Bits → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 * natOf bs

/-- The low `w` bits of `n`, least significant first. -/
def bitsOfNat : Nat → Nat → Bits
  | 0, _ => []
  | w + 1, n => (n % 2 == 1) :: bitsOfNat w (n / 2)

@[simp] theorem length_bitsOfNat (w n : Nat) : (bitsOfNat w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [bitsOfNat, ih]

theorem natOf_lt (b : Bits) : natOf b < 2 ^ b.length := by
  induction b with
  | nil => simp [natOf]
  | cons x b ih =>
    have := Bool.toNat_le x
    simp only [natOf, List.length_cons, Nat.pow_succ]
    omega

theorem natOf_bitsOfNat (w n : Nat) : natOf (bitsOfNat w n) = n % 2 ^ w := by
  induction w generalizing n with
  | zero => simp [bitsOfNat, natOf, Nat.mod_one]
  | succ w ih =>
    simp only [bitsOfNat, natOf, ih]
    have h1 : (n % 2 == 1).toNat = n % 2 := by
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]
    rw [h1, Nat.pow_succ, Nat.mul_comm (2 ^ w) 2, Nat.mod_mul]

theorem bitsOfNat_natOf (b : Bits) : bitsOfNat b.length (natOf b) = b := by
  induction b with
  | nil => rfl
  | cons x b ih =>
    simp only [List.length_cons, bitsOfNat, natOf]
    have h2 : (x.toNat + 2 * natOf b) / 2 = natOf b := by cases x <;> simp <;> omega
    rw [h2, ih]
    try (cases x <;> simp)

theorem natOf_inj {a b : Bits} (hl : a.length = b.length) (h : natOf a = natOf b) : a = b := by
  rw [← bitsOfNat_natOf a, ← bitsOfNat_natOf b, hl, h]

theorem bitsOfNat_mod (w n : Nat) : bitsOfNat w (n % 2 ^ w) = bitsOfNat w n := by
  have h := natOf_inj (a := bitsOfNat w (n % 2 ^ w)) (b := bitsOfNat w n) (by simp)
  apply h
  rw [natOf_bitsOfNat, natOf_bitsOfNat, Nat.mod_mod]

/-- A 255-bit word. -/
def word (n : Nat) : Bits := bitsOfNat 255 n

@[simp] theorem length_word (n : Nat) : (word n).length = 255 := length_bitsOfNat _ _

theorem natOf_word (n : Nat) (h : n < 2 ^ 255) : natOf (word n) = n := by
  rw [word, natOf_bitsOfNat, Nat.mod_eq_of_lt h]

/-! ## The prime, and the arithmetic specifications of the word circuits -/

/-- p = 2^255 − 19 (`WordMask.P`, `FieldDag.modulus`). -/
abbrev P : Nat := TlsMpc.WordMask.P

theorem P_eq : P = 57896044618658097711785492504343953926634992332820282019728792003956564819949 := rfl
theorem P_modulus : P = modulus := TlsMpc.WordMask.P_eq_modulus
theorem P_lt_two_pow : P < 2 ^ 255 := by decide
theorem two_pow_eq : 2 ^ 255 = P + 19 := by decide

/-- `modAdd x y` (`WordMask.modAdd`: `condSub` of the 256-bit sum) on any two 255-bit values. -/
def addModSpec (x y : Nat) : Nat :=
  if P ≤ x + y then (x + y - P) % 2 ^ 255 else (x + y) % 2 ^ 255

/-- On canonical values it is addition mod p (`WordMask.modAdd_val`). -/
theorem addModSpec_canonical (x y : Nat) (hx : x < P) (hy : y < P) : addModSpec x y = (x + y) % P := by
  have h := two_pow_eq
  unfold addModSpec
  split
  · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- `reduceOnce` (`u mod p` for any 255-bit `u`). -/
def reduceSpec (u : Nat) : Nat := if P ≤ u then u - P else u

theorem reduceSpec_eq (u : Nat) (hu : u < 2 ^ 255) : reduceSpec u = u % P := by
  have h := two_pow_eq
  unfold reduceSpec
  split
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]

/-- The first and second 255-bit words of a 510-bit input. -/
def wordX (v : Bits) : Nat := natOf (v.take 255)
def wordY (v : Bits) : Nat := natOf ((v.drop 255).take 255)

/-- `modadd` (one copy): `modAdd X Y`. -/
def modaddEval (v : Bits) : Bits := word (addModSpec (wordX v) (wordY v))
/-- `finalize-mask`: `modAdd X Y`, then the flag "both canonical". -/
def finalizeMaskEval (v : Bits) : Bits :=
  modaddEval v ++ [decide (wordX v < P) && decide (wordY v < P)]
/-- `finalize-bits`: `X xor Y` (bitwise), then the flag "both canonical and both at least 32". -/
def finalizeBitsEval (v : Bits) : Bits :=
  List.zipWith (· ^^ ·) (v.take 255) ((v.drop 255).take 255) ++
    [decide (wordX v < P) && decide (wordY v < P) && decide (32 ≤ wordX v) && decide (32 ≤ wordY v)]
/-- `into-field`: `modAdd (reduceOnce X) Y`. -/
def intoFieldEval (v : Bits) : Bits := word (addModSpec (reduceSpec (wordX v)) (wordY v))
/-- `xor-bit`: one XOR. -/
def xorBitEval (v : Bits) : Bits := [v.getD 0 false ^^ v.getD 1 false]
/-- `swap-bits` (`X25519SwapBits.circuit`): output `k` is the swap bit of ladder step `k + 2`. -/
def swapBit (v : Bits) (t : Nat) : Bool :=
  if t = 2 then v.getD 3 false
  else if t = 253 then !(v.getD 253 false)
  else (v.getD (t + 1) false ^^ v.getD t false)
def swapBitsEval (v : Bits) : Bits := (List.range 252).map fun k => swapBit v (k + 2)

/-! ## Circuit names and marks (the Rust loader's `WORD_CIRCUITS`) -/

def modaddName : Bytes := ascii "modadd"
def modaddOpenName : Bytes := ascii "modadd-open"
def finalizeMaskName : Bytes := ascii "finalize-mask"
def finalizeBitsName : Bytes := ascii "finalize-bits"
def intoFieldOpenName : Bytes := ascii "into-field-open"
def xorBitName : Bytes := ascii "xor-bit"
def xorBitOpenName : Bytes := ascii "xor-bit-open"
def swapBitsName : Bytes := ascii "swap-bits"

def wordNever : List Mark := List.replicate 255 .never
def wordPub : List Mark := List.replicate 255 .pub
def finalMarks : List Mark := wordNever ++ [.pub]

def modaddC : Circuit := ⟨510, wordNever, modaddEval⟩
def modaddOpenC : Circuit := ⟨510, wordPub, modaddEval⟩
def finalizeMaskC : Circuit := ⟨510, finalMarks, finalizeMaskEval⟩
def finalizeBitsC : Circuit := ⟨510, finalMarks, finalizeBitsEval⟩
def intoFieldOpenC : Circuit := ⟨510, wordPub, intoFieldEval⟩
def xorBitC : Circuit := ⟨2, [.never], xorBitEval⟩
def xorBitOpenC : Circuit := ⟨2, [.pub], xorBitEval⟩
def swapBitsC : Circuit := ⟨256, List.replicate 252 .never, swapBitsEval⟩

/-- **The word circuits the S10 scripts run** are, under their names, the specifications above
(with the loader's marks). With `modAdd_exact` and its siblings below, this is exactly the T2
trust that the pinned files of `lower_word_circuits.py` compute `TlsMpc/WordMask.lean`'s and
`TlsMpc/X25519SwapBits.lean`'s circuits. -/
structure WordLoaded (E : Env) : Prop where
  modadd : E.circuits modaddName = some modaddC
  modaddOpen : E.circuits modaddOpenName = some modaddOpenC
  finalizeMask : E.circuits finalizeMaskName = some finalizeMaskC
  finalizeBits : E.circuits finalizeBitsName = some finalizeBitsC
  intoFieldOpen : E.circuits intoFieldOpenName = some intoFieldOpenC
  xorBit : E.circuits xorBitName = some xorBitC
  xorBitOpen : E.circuits xorBitOpenName = some xorBitOpenC
  swapBits : E.circuits swapBitsName = some swapBitsC

/-! ## The Lean circuits compute these specifications on every input -/

section Exact

open TlsMpc.BoolDag TlsMpc.WordMask

theorem map_eval_bits (env : Nat → Bool) (es : List Expr) :
    es.map (Expr.eval env) = bitsOfNat es.length (val env es) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons, List.length_cons, bitsOfNat, val, ih]
    have h2 : ((e.eval env).toNat + 2 * val env es) / 2 = val env es := by
      cases e.eval env <;> simp <;> omega
    rw [h2]
    cases e.eval env <;> simp

theorem val_lt' (env : Nat → Bool) (bits : List Expr) : val env bits < 2 ^ bits.length :=
  TlsMpc.WordMask.val_lt env bits

/-- `condSub` on ANY 256-bit `s` (not only `s < 2p`, as `WordMask.condSub_val` requires). -/
theorem condSub_exact (env : Nat → Bool) (s : List Expr) (hlen : s.length = 256) :
    val env (condSub s) = if P ≤ val env s then (val env s - P) % 2 ^ 255 else val env s % 2 ^ 255 := by
  have hP : P = 57896044618658097711785492504343953926634992332820282019728792003956564819949 := rfl
  have hc : (constBits 256 (2 ^ 256 - P)).length = s.length := by rw [constBits_length, hlen]
  have h := addBits_val env s (constBits 256 (2 ^ 256 - P)) (.const false) hc.symm
  have hl := addBits_length s (constBits 256 (2 ^ 256 - P)) (.const false) hc.symm
  have hlow := val_lt' env (addBits s (constBits 256 (2 ^ 256 - P)) (.const false)).1
  have hs := val_lt' env s
  rw [hl, hlen] at hlow
  rw [hlen] at hs
  rw [constBits_val, hlen] at h
  simp only [Expr.eval, Bool.toNat_false, Nat.add_zero] at h
  unfold condSub
  rw [mux_val env _ _ _ (by simp [hl, hlen]), val_take, val_take]
  generalize (addBits s (constBits 256 (2 ^ 256 - P)) (.const false)).2.eval env = carry at h
  generalize val env (addBits s (constBits 256 (2 ^ 256 - P)) (.const false)).1 = low at h hlow
  generalize val env s = x at h hs ⊢
  rw [hP] at h ⊢
  cases carry
  · simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at h
    simp only [Bool.false_eq_true, if_false]
    rw [if_neg (by omega)]
  · simp only [Bool.toNat_true, Nat.mul_one] at h
    simp only [if_true]
    rw [if_pos (by omega)]
    have e : low = x - 57896044618658097711785492504343953926634992332820282019728792003956564819949 := by
      omega
    rw [e]

/-- **`modAdd` computes `addModSpec` on every pair of 255-bit words.** -/
theorem modAdd_exact (env : Nat → Bool) (x y : List Expr) (hx : x.length = 255) (hy : y.length = 255) :
    val env (modAdd x y) = addModSpec (val env x) (val env y) := by
  have h := addBits_val env x y (.const false) (by rw [hx, hy])
  have hl := addBits_length x y (.const false) (by rw [hx, hy])
  simp only [Expr.eval, Bool.toNat_false, Nat.add_zero] at h
  have hv : val env ((addBits x y (.const false)).1 ++ [(addBits x y (.const false)).2]) =
      val env x + val env y := by
    rw [val_append, hl]
    simp only [val, Nat.mul_zero, Nat.add_zero]
    rw [← h]
  unfold modAdd
  rw [condSub_exact env _ (by simp [hl, hx]), hv]
  rfl

/-- **`reduceOnce` computes `reduceSpec`.** -/
theorem reduceOnce_exact (env : Nat → Bool) (u : List Expr) (hu : u.length = 255) :
    val env (reduceOnce u) = reduceSpec (val env u) := by
  have hlt := val_lt' env u
  rw [hu] at hlt
  rw [reduceOnce_val env u hu, reduceSpec_eq _ hlt]

end Exact

/-! ## Field programs (V3) the scripts name -/

open TlsMpc.FieldDag.V3 (Program OMark)

def bitCheckName : Bytes := ascii "field-bit-check"
def bitXorName : Bytes := ascii "field-bit-xor"
def recomposeName : Bytes := ascii "field-recompose"
def maskSubName : Bytes := ascii "field-mask-sub"

/-- **The program `p` computes `f` without masks**: `inputs` data inputs, no mask, outputs marked
`marks`, and every evaluation succeeds with outputs `f input` and no opening. -/
def Computes (p : Program) (inputs : Nat) (marks : List OMark) (f : (Nat → F) → List F) : Prop :=
  p.inputs = inputs ∧ p.masks = 0 ∧ p.outputs.map (·.2) = marks ∧
    ∀ input mask, TlsMpc.FieldDag.V3.eval p input mask = some (f input, [])

/-- `field-mask-sub` (S10, natively V3): `v − f` (inputs 0, 1), public. Field to word opens it. -/
def maskSub : Program where
  inputs := 2
  masks := 0
  rows := [.input 0, .input 1, .sub 0 1]
  outputs := [(2, .pub)]

theorem maskSub_valid : maskSub.valid = true := by decide
theorem maskSub_masksOk : maskSub.masksOk = true := by decide
theorem maskSub_declares : maskSub.declares [.check] = true ∧ maskSub.publicOutputs = [0] := by decide

set_option maxRecDepth 20000 in
theorem maskSub_computes : Computes maskSub 2 [.pub] (fun i => [i 0 - i 1]) :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

/-- The value of `field-bit-xor` (`FieldBits.bitXor`): `a + b − 2ab`. -/
def bitXorValue (a b : F) : F := a + b - TlsMpc.FieldDag.ofNat 2 * (a * b)

theorem bitXor_eval (i : Nat → F) : TlsMpc.FieldBits.bitXor.eval i = bitXorValue (i 0) (i 1) := rfl

theorem bitXorValue_bits (a b : Bool) :
    bitXorValue (X25519.bitValue a) (X25519.bitValue b) = X25519.bitValue (a ^^ b) := by
  have := TlsMpc.FieldBits.bitXor_bits (fun j => if j = 0 then X25519.bitValue a else X25519.bitValue b) a b
    rfl rfl
  rw [bitXor_eval] at this
  exact this

/-- **The programs the S10 scripts run** are, under their names, programs computing these values
without masks. `computes_of_decl` discharges the three exported ones from their declarations
(`FieldProgramsV3.find`) and `masks = 0`; `field-mask-sub` is `maskSub` itself (its text is
Lean's `render maskSub`, pinned by its hash). -/
structure ProgsLoaded (E : Env) : Prop where
  bitCheck : ∃ p, E.programs bitCheckName = some p ∧
    Computes p 1 [.pub] (fun i => [i 0 * (i 0 - TlsMpc.FieldDag.ofNat 1)])
  bitXor : ∃ p, E.programs bitXorName = some p ∧ Computes p 2 [.never] (fun i => [bitXorValue (i 0) (i 1)])
  recompose : ∃ p, E.programs recomposeName = some p ∧
    Computes p 256 [.pub] (fun i => [TlsMpc.FieldBits.hornerValue ((List.range 255).map i) - i 255])
  maskSub : E.programs maskSubName = some maskSub

/-! ### A program without masks never aborts -/

open TlsMpc.FieldDag.V3 in
theorem runFrom_some (rows : List Row) (input mask : Nat → F) :
    ∀ (rs : List Row) (s : State), (∀ r ∈ rs, r.mask? = none) →
      ∃ s', rs.foldlM (step rows input mask) s = some s' := by
  intro rs
  induction rs with
  | nil => intro s _; exact ⟨s, rfl⟩
  | cons r rs ih =>
    intro s h
    have hr : r.mask? = none := h r (by simp)
    have hrs : ∀ r' ∈ rs, r'.mask? = none := fun r' hr' => h r' (by simp [hr'])
    simp only [List.foldlM_cons, Option.bind_eq_bind]
    cases r with
    | div a b m => simp [Row.mask?] at hr
    | zdiv a b m => simp [Row.mask?] at hr
    | input i => exact ih _ hrs
    | const n => exact ih _ hrs
    | add a b => exact ih _ hrs
    | sub a b => exact ih _ hrs
    | mul a b => exact ih _ hrs
    | flag k =>
      simp only [step]
      split <;> exact ih _ hrs

open TlsMpc.FieldDag.V3 in
/-- With `masks = 0` (and `masksOk`, true of every exported and parsed program) no row names a
mask, so the evaluation succeeds and opens nothing. -/
theorem eval_some_of_masks (p : Program) (hok : p.masksOk = true) (hm : p.masks = 0) (input mask : Nat → F) :
    ∃ outs, eval p input mask = some (outs, []) := by
  have hu : p.maskUses = [] := by
    simp only [Program.masksOk, beq_iff_eq] at hok
    rw [hok, hm]
    rfl
  have hnone : ∀ r ∈ p.rows, r.mask? = none := by
    intro r hr
    cases h : r.mask? with
    | none => rfl
    | some m =>
      have : m ∈ p.maskUses := List.mem_filterMap.mpr ⟨r, hr, h⟩
      rw [hu] at this
      cases this
  obtain ⟨s, hs⟩ := runFrom_some p.rows input mask p.rows {} hnone
  have ho := foldlM_opened p.rows input mask p.rows {} s hs
  have hf : (p.rows.filterMap Row.mask?) = [] := hu
  rw [hf] at ho
  have hopen : s.opened = [] := by
    have : s.opened.length = 0 := by simpa using ho
    exact List.eq_nil_of_length_eq_zero this
  refine ⟨p.outputs.map fun o => get s.vals o.1, ?_⟩
  simp only [eval, runFrom, hs, Option.map_some, hopen]

/-- **An exported program computes its declaration's expressions** (with `FieldInverse`), when its
V3 file has no mask (`masks = 0`, which the loader's parser reads off the header). -/
theorem computes_of_decl (hinv : TlsMpc.FieldDag.V3.FieldInverse) (d : TlsMpc.FieldProgramsV3.Decl)
    (hd : d.ok = true) (p : Program) (hp : d.program = some p) (hm : p.masks = 0) :
    Computes p d.inputs (d.roles.map TlsMpc.FieldDag.V3.Role.mark) (fun i => d.exprs.map (TlsMpc.FieldDag.Expr.eval i)) := by
  obtain ⟨hok, hdecl, -⟩ := TlsMpc.FieldProgramsV3.Decl.checks d hd p hp
  obtain ⟨a, -, rfl⟩ := TlsMpc.FieldProgramsV3.Decl.program_eq hp
  refine ⟨rfl, hm, ?_, fun input mask => ?_⟩
  · simp only [TlsMpc.FieldDag.V3.Program.declares, Bool.and_eq_true, beq_iff_eq] at hdecl
    exact hdecl.1
  · obtain ⟨outs, ho⟩ := eval_some_of_masks _ hok hm input mask
    have hv := TlsMpc.FieldProgramsV3.Decl.values hinv d _ hp input mask outs [] ho
    rw [ho, hv]

/-! ## The mask pool -/

/-- A word mask: 255 Boolean bits `w` and a field element `f` with `val(w) = f` (P-CUT (a)). -/
structure WordMask where
  bits : BoolH
  field : FieldH
  deriving DecidableEq, Repr

/-- A bit pair: a one-bit Boolean handle and a field element holding the same bit (P-PAIR). -/
structure BitPair where
  bit : BoolH
  field : FieldH
  deriving DecidableEq, Repr

/-- **The pool** a session's conversions draw from (Lean-side public state: names of handles). -/
structure MaskPool where
  words : List WordMask := []
  bits : List BitPair := []
  deriving DecidableEq, Repr

namespace MaskPool

/-- Take one word mask: the first, and the pool without it. -/
def takeWord (p : MaskPool) : Option (WordMask × MaskPool) :=
  match p.words with
  | m :: rest => some (m, { p with words := rest })
  | [] => none

/-- Take `n` bit pairs. -/
def takeBits (p : MaskPool) (n : Nat) : Option (List BitPair × MaskPool) :=
  if n ≤ p.bits.length then some (p.bits.take n, { p with bits := p.bits.drop n }) else none

/-- Masks taken one after the other, `k` times. -/
def takes : Nat → MaskPool → Option (List WordMask × MaskPool)
  | 0, p => some ([], p)
  | k + 1, p => do
    let (m, p) ← p.takeWord
    let (ms, p) ← takes k p
    pure (m :: ms, p)

/-- The pool has no entry twice (true of every pool `Masks.generate` returns: its handles are a
fresh block). -/
def Distinct (p : MaskPool) : Prop := p.words.Nodup ∧ p.bits.Nodup

/-- **P-CUT (h), one take:** the mask taken is not in the pool returned, and that pool is still
duplicate free. -/
theorem takeWord_fresh {p p' : MaskPool} {m : WordMask} (hd : p.Distinct) (h : p.takeWord = some (m, p')) :
    m ∉ p'.words ∧ p'.Distinct ∧ p'.bits = p.bits ∧ p.words = m :: p'.words := by
  unfold takeWord at h
  split at h
  · next m' rest hw =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hn := hd.1
    rw [hw, List.nodup_cons] at hn
    exact ⟨hn.1, ⟨hn.2, hd.2⟩, rfl, hw⟩
  · cases h

theorem takeBits_fresh {p p' : MaskPool} {n : Nat} {bs : List BitPair} (hd : p.Distinct)
    (h : p.takeBits n = some (bs, p')) :
    (∀ b ∈ bs, b ∉ p'.bits) ∧ bs.Nodup ∧ bs.length = n ∧ p'.Distinct ∧ p'.words = p.words ∧
      p.bits = bs ++ p'.bits := by
  unfold takeBits at h
  split at h
  · next hn =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hnd := hd.2
    rw [← List.take_append_drop n p.bits] at hnd
    rw [List.nodup_append] at hnd
    refine ⟨fun b hb hb' => hnd.2.2 b hb b hb' rfl, hnd.1, by simp; omega, ⟨hd.1, hnd.2.1⟩, rfl, ?_⟩
    exact (List.take_append_drop n p.bits).symm
  · cases h

/-- **P-CUT (h), any number of takes:** the masks handed out are pairwise distinct, none of them is
left in the pool, and they are the pool's first entries. -/
theorem takes_distinct : ∀ (k : Nat) (p p' : MaskPool) (ms : List WordMask), p.Distinct →
    takes k p = some (ms, p') → ms.Nodup ∧ (∀ m ∈ ms, m ∉ p'.words) ∧ p'.Distinct ∧ p.words = ms ++ p'.words
  | 0, p, p', ms, hd, h => by
    simp only [takes, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨List.nodup_nil, by simp, hd, rfl⟩
  | k + 1, p, p', ms, hd, h => by
    simp only [takes, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨⟨m, p1⟩, h1, ⟨ms', p2⟩, h2, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨hm, hd1, -, hw1⟩ := takeWord_fresh hd h1
    obtain ⟨hn, hout, hd2, hw2⟩ := takes_distinct k p1 p2 ms' hd1 h2
    refine ⟨List.nodup_cons.mpr ⟨fun hin => hm (by rw [hw2]; exact List.mem_append_left _ hin), hn⟩,
      fun x hx => ?_, hd2, by rw [hw1, hw2]; rfl⟩
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · intro hx'
      exact hm (by rw [hw2]; exact List.mem_append_right _ hx')
    · exact hout x hx

end MaskPool

end TlsMpc.Node.Flows.Conv
