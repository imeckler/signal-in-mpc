import TlsMpc.Node.Local.Field
import TlsMpc.EdwardsHinted
import TlsMpc.EstablishField
import TlsMpc.EdwardsShare

/-!
# Local curve arithmetic: Edwards points in the clear

REORGANIZATION_PLAN.md stage S11, `Local/Edwards.lean`. Replaces, for the Lean flows, libsodium
(`crypto_core_ed25519_add/sub/is_valid_point`, `crypto_scalarmult_ed25519_*_noclamp`,
`crypto_sign_ed25519_pk_to_curve25519`, `crypto_core_ed25519_random`) and the OpenSSL bignum
classes `LocalCurve` (`split_ecdh.h`) and `LocalField`, `Ed` (`hinted_points.h`). Run by a node on
PUBLIC points and on its OWN secrets only (its scalar's multiples, its mask points and hints).

THE FORMULAS ARE THE PROGRAMS' FORMULAS. The curve is the twisted Edwards form of Curve25519,
`−x² + y² = 1 + d·x²·y²`, `d = −121665/121666`, the form of `EdwardsAffine` and `EdwardsHinted`:
  * affine addition `add` IS `EdwardsAffine.pointAddValue` (`add_eq`), with the square and
    multiply inverse (`Field.inv_eq`);
  * extended coordinates: `extAdd` IS `EdwardsHinted.extAddValue` (the same function), doubling is
    `extAdd p p` as in the programs' `doublings`, and `toAffine` is `toAffineValue` (`toAffine_eq`);
  * scalar multiplication `mulExt` is double-and-add with exactly those steps (`mulBits_cons`).
So the Mathlib package's group-law theorems about `pointAddValue` / `extAddValue`
(`proofs/` `affine_pointAddValue`, `extRep_extAddValue`, R7) apply to every value computed here.

THE MONTGOMERY MAP is `u = (1 + y)/(1 − y)` (`montU`; the form `EdwardsAffine.offsetSum` outputs and
`proofs/` `montU` is about: `montU_eq`), and its inverse `y = (u − 1)/(u + 1)` (`liftU`).

PROVED: `add_eq`, `toAffine_eq`, `montU_eq`, `mulBits_cons`/`mulBits_nil`, `onCurve_iff` (the check
is the programs' `curveCheck` / `EdwardsShare.onCurve` value), `toAffineAll_spec` (batched
inversion: each affine point represents its extended point), `root_spec` (the lift's public root),
`recoverPublic_eq` (the local evaluation of `xeddsa-recover` is the program's expressions'
value). TESTED (`node_worker/tests/s11_curve.rs`): agreement with curve25519-dalek on encodings,
sums, scalar multiples, the Montgomery map and validity (Lean-generated vectors).
No I/O; no emitter imports this module.
-/

namespace TlsMpc.Node.Local.Edwards

open TlsMpc.FieldDag (F modulus ofNat inverse)
open TlsMpc.Node.Local.Field
open TlsMpc.Node.Engine (Bytes Party)

abbrev Value := TlsMpc.EdwardsAffine.Value
abbrev ExtV := TlsMpc.EdwardsHinted.ExtV

/-! ## Constants -/

/-- `d = −121665/121666` (`XEdDsaField.d`). -/
def dK : F := ofNat TlsMpc.Signal.XEdDsaField.d

theorem dK_scaled : dK * ofNat 121666 = 0 - ofNat 121665 := by decide

/-- The base point B (`y = 4/5`, x even): `EdwardsHinted.baseX`, `baseY`. -/
def base : Value := (ofNat TlsMpc.EdwardsHinted.baseX, ofNat TlsMpc.EdwardsHinted.baseY)

/-- The neutral element `(0, 1)`. -/
def neutral : Value := (ofNat 0, ofNat 1)

/-- The prime order ℓ of B. -/
def ell : Nat := 2 ^ 252 + 27742317777372353535851937790883648493

/-- `1/8 mod ℓ` (the torsion hint's scalar, `hinted_points.h` `torsion`). -/
def eighth : Nat := 2713877091499598330239944961141122840321418634767465352250731601857045344121

theorem eighth_spec : eighth * 8 % ell = 1 := by decide

/-- `√(−486664)` (`EdwardsHinted.sqrtMinusA2`): the constant of the Montgomery-to-Edwards map. -/
def sA2 : F := ofNat TlsMpc.EdwardsHinted.sqrtMinusA2

/-! ## Affine arithmetic (the formulas of `EdwardsAffine`) -/

/-- Complete twisted Edwards addition, scaled by 121666 (`EdwardsAffine.pointAddValue`), with the
square and multiply inverse. -/
def add (p q : Value) : Value :=
  let t := ofNat 121665 * (p.1 * q.1 * (p.2 * q.2))
  (ofNat 121666 * (p.1 * q.2 + p.2 * q.1) * inv (ofNat 121666 - t),
   ofNat 121666 * (p.2 * q.2 + p.1 * q.1) * inv (ofNat 121666 + t))

/-- **`add` is the programs' addition.** -/
theorem add_eq (p q : Value) : add p q = TlsMpc.EdwardsAffine.pointAddValue p q := by
  simp only [add, TlsMpc.EdwardsAffine.pointAddValue, inv_eq]

def neg (p : Value) : Value := (ofNat 0 - p.1, p.2)

def sub (p q : Value) : Value := add p (neg q)

/-- Whether `p` satisfies the curve equation, in the scaled form of the programs' check:
`121666·(y² − x² − 1) + 121665·x²·y² = 0`. -/
def curveValue (p : Value) : F :=
  ofNat 121666 * (p.2 * p.2 - p.1 * p.1 - ofNat 1) + ofNat 121665 * (p.1 * p.1 * (p.2 * p.2))

def onCurve (p : Value) : Bool := curveValue p == 0

/-- **The check is the programs' check value** (`EdwardsShare.onCurve`, `EdwardsHinted.curveCheck`). -/
theorem onCurve_iff (p : Value) :
    onCurve p = true ↔ TlsMpc.EdwardsShare.onCurve.eval (fun i => if i = 0 then p.1 else p.2) = 0 := by
  rw [TlsMpc.EdwardsShare.onCurve_eval]
  simp [onCurve, curveValue]

theorem curveValue_check (p : Value) :
    (TlsMpc.EdwardsHinted.curveCheck (TlsMpc.EdwardsAffine.inputPoint 0)).eval
      (fun i => if i = 0 then p.1 else p.2) = curveValue p := rfl

/-! ## Extended coordinates (the formulas of `EdwardsHinted`) -/

def ofAffine (p : Value) : ExtV := TlsMpc.EdwardsHinted.ofAffineValue p

/-- Complete unified addition in extended coordinates: `EdwardsHinted.extAddValue` itself. -/
def extAdd (p q : ExtV) : ExtV := TlsMpc.EdwardsHinted.extAddValue p q

theorem extAdd_eq (p q : ExtV) : extAdd p q = TlsMpc.EdwardsHinted.extAddValue p q := rfl

def extNeutral : ExtV := TlsMpc.EdwardsHinted.neutralValue

def toAffine (p : ExtV) : Value := (p.x * inv p.z, p.y * inv p.z)

/-- **`toAffine` is the programs' `toAffineValue`.** -/
theorem toAffine_eq (p : ExtV) : toAffine p = TlsMpc.EdwardsHinted.toAffineValue p := by
  simp only [toAffine, TlsMpc.EdwardsHinted.toAffineValue, inv_eq]

/-- Double-and-add over bits, most significant first: per bit, double the accumulator
(`extAdd acc acc`, the programs' doubling), then add `P` when the bit is set. -/
def mulBits (P : ExtV) : List Bool → ExtV → ExtV
  | [], acc => acc
  | b :: bs, acc =>
    let d := extAdd acc acc
    mulBits P bs (if b then extAdd d P else d)

theorem mulBits_nil (P acc : ExtV) : mulBits P [] acc = acc := rfl

theorem mulBits_cons (P acc : ExtV) (b : Bool) (bs : List Bool) :
    mulBits P (b :: bs) acc =
      mulBits P bs (if b then TlsMpc.EdwardsHinted.extAddValue (TlsMpc.EdwardsHinted.extAddValue acc acc) P
        else TlsMpc.EdwardsHinted.extAddValue acc acc) := rfl

/-- The bits of `k`, most significant first (`log₂ k + 1` of them). -/
def bitsMSB (k : Nat) : List Bool := (List.range (Nat.log2 k + 1)).reverse.map k.testBit

/-- `k·P` in extended coordinates. -/
def mulExt (k : Nat) (P : ExtV) : ExtV := mulBits P (bitsMSB k) extNeutral

/-- `k·P` for an affine `P`. -/
def mul (k : Nat) (P : Value) : Value := toAffine (mulExt k (ofAffine P))

/-- `16·P`: four doublings. -/
def times16 (p : ExtV) : ExtV :=
  let p2 := extAdd p p
  let p4 := extAdd p2 p2
  let p8 := extAdd p4 p4
  extAdd p8 p8

/-! ## Batched inversion (Montgomery's trick), checked -/

/-- The backward pass: from `acc = (z₁⋯zᵢ)⁻¹`, emit `zᵢ⁻¹ = acc·(z₁⋯zᵢ₋₁)` and move to
`acc·zᵢ`. Arguments reversed: `zs = [zₙ, …]`, `ps = [z₁⋯zₙ₋₁, …, 1]`. -/
def backward : List F → List F → F → List F → List F
  | z :: zs, p :: ps, acc, out => backward zs ps (acc * z) ((acc * p) :: out)
  | _, _, _, out => out

/-- The inverses of `zs` with one field inversion; `none` unless every `z·w = 1` checks (so a zero
`z` gives `none`, never a wrong value). -/
def invAll (zs : List F) : Option (List F) :=
  let prefixes := zs.scanl (· * ·) (ofNat 1)
  let total := prefixes.getLastD (ofNat 1)
  let ws := backward zs.reverse prefixes.dropLast.reverse (inv total) []
  if ws.length = zs.length ∧ (zs.zip ws).all (fun e => e.1 * e.2 == ofNat 1) then some ws else none

theorem invAll_spec (zs ws : List F) (h : invAll zs = some ws) :
    ws.length = zs.length ∧ ∀ e ∈ zs.zip ws, e.1 * e.2 = ofNat 1 := by
  unfold invAll at h
  dsimp only at h
  split at h
  · next hc =>
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨hc.1, fun e he => ?_⟩
    have := List.all_eq_true.mp hc.2 e he
    simpa using this
  · cases h

/-- Many extended points to affine with one inversion (`none` if a `Z` is zero). -/
def toAffineAll (es : List ExtV) : Option (List Value) :=
  match invAll (es.map (·.z)) with
  | some ws => some ((es.zip ws).map fun e => (e.1.x * e.2, e.1.y * e.2))
  | none => none

/-- **Each affine point represents its extended point**: `x'·Z = X` and `y'·Z = Y`. -/
theorem toAffineAll_spec (es : List ExtV) (vs : List Value) (h : toAffineAll es = some vs) :
    vs.length = es.length ∧ ∀ i (hi : i < es.length) (hv : i < vs.length),
      vs[i].1 * es[i].z = es[i].x ∧ vs[i].2 * es[i].z = es[i].y := by
  unfold toAffineAll at h
  split at h
  · next ws hw =>
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨hl, hm⟩ := invAll_spec _ _ hw
    simp only [List.length_map] at hl
    refine ⟨by simp [hl], fun i hi hv => ?_⟩
    have hwi : i < ws.length := by rw [hl]; exact hi
    have he : ((es.map (·.z))[i]'(by simpa using hi), ws[i]) ∈ (es.map (·.z)).zip ws :=
      List.mem_iff_getElem.mpr ⟨i, by simp [hl, hi], by simp⟩
    have h1 := hm _ he
    simp only [List.getElem_map] at h1
    have hone : (ofNat 1 : F) = 1 := rfl
    rw [hone] at h1
    simp only [List.getElem_map, List.getElem_zip]
    constructor <;> grind
  · cases h

/-! ## Encodings (Ed25519 compressed points) and the Montgomery map -/

/-- `y`, little-endian, with the parity of `x` in the top bit (libsodium's encoding). -/
def encode (p : Value) : Bytes :=
  let b := toBytes p.2
  b.set 31 (b.getD 31 0 ||| (if p.1.val % 2 = 1 then 128 else 0))

/-- The `x` of a `y` (`x² = (y² − 1)/(d·y² + 1)`) with the given parity; `none` off the curve or for
`x = 0` with the odd flag. -/
def xOfY (y : F) (odd : Bool) : Option F :=
  let yy := y * y
  match sqrt ((yy - ofNat 1) * inv (dK * yy + ofNat 1)) with
  | none => none
  | some x => if x = 0 ∧ odd then none else some (withParity x odd)

/-- Decode a compressed point (canonical `y` required). -/
def decode (b : Bytes) : Option Value :=
  if b.length = 32 then
    let odd := b.getD 31 0 / 128 == 1
    match ofBytes (b.set 31 (b.getD 31 0 &&& 127)) with
    | none => none
    | some y => (xOfY y odd).map fun x => (x, y)
  else none

/-- The Montgomery coordinate `u = (1 + y)/(1 − y)` (`crypto_sign_ed25519_pk_to_curve25519`). -/
def montU (p : Value) : F := (ofNat 1 + p.2) * inv (ofNat 1 - p.2)

/-- **The form of `EdwardsAffine.offsetSum`'s output and of `proofs/` `montU`.** -/
theorem montU_eq (p : Value) : montU p = (ofNat 1 + p.2) * inverse (ofNat 1 - p.2) := by
  rw [montU, inv_eq]

/-- A point with Montgomery coordinate `u` and even `x` (`split_ecdh.h` `LocalCurve.lift` then
`coordinates`): `y = (u − 1)/(u + 1)`; `none` for `u = −1` or off the curve. -/
def liftU (u : F) : Option Value :=
  let bottom := u + ofNat 1
  if bottom = 0 then none
  else (xOfY ((u - ofNat 1) * inv bottom) false).map fun x => (x, (u - ofNat 1) * inv bottom)

/-! ## Validity, torsion, random points -/

def isNeutral (p : Value) : Bool := p.1 == ofNat 0 && p.2 == ofNat 1

/-- libsodium's `crypto_core_ed25519_is_valid_point` on a decoded point: on the curve, not of small
order (8·P ≠ 0), and in the prime-order subgroup (ℓ·P = 0). -/
def isValid (p : Value) : Bool :=
  onCurve p && !isNeutral (mul 8 p) && isNeutral (mul ell p)

/-- A point of order 8 (`hinted_points.h` `Ed::torsion`), decoded from its libsodium encoding. -/
def torsionBytes : Bytes :=
  [0xc7, 0x17, 0x6a, 0x70, 0x3d, 0x4d, 0xd8, 0x4f, 0xba, 0x3c, 0x0b, 0x76, 0x0d, 0x10, 0x67, 0x0f,
   0x2a, 0x20, 0x53, 0xfa, 0x2c, 0x39, 0xcc, 0xc6, 0x4e, 0xc7, 0xfd, 0x77, 0x92, 0xac, 0x03, 0x7a]

def torsion8 : Value := (decode torsionBytes).getD neutral

/-- A point uniform over the whole group of the curve (`Ed::random`: the prime-order part and the 8
torsion points) from uniform `r` (mod ℓ) and `t` (mod 8): `r·B + t·T₈`. The group of Curve25519 is
cyclic of order 8ℓ, so this map from Z/ℓ × Z/8 is a bijection onto it (not proved here). -/
def randomPoint (r t : Nat) : Value := add (mul (r % ell) base) (mul (t % 8) torsion8)

/-! ## Hints (`hinted_points.h` `hints`, `torsion`) -/

/-- The point whose multiples this party hints: A enters multiples of `Z − M_A`, B of `M_B`
(their difference is the lifted point `P`, since `Z = P + M_A + M_B`). -/
def hintBase (me : Party) (z mask : Value) : Value :=
  match me with
  | .a => sub z mask
  | .b => mask

/-- The 63 window bases `16^w·Q`, `w = 1 … 63`, in extended coordinates. -/
def windowBases (q : Value) : List ExtV :=
  ((List.range 63).foldl (fun (st : List ExtV × ExtV) _ =>
    let next := times16 st.2
    (next :: st.1, next)) ([], ofAffine q)).1.reverse

/-- This party's hint coordinates for one lifted point: `x, y` of `16^w·Q` for `w = 1 … 63`
(126 elements); `none` only if a projective `Z` were zero. -/
def hints (me : Party) (z mask : Value) : Option (List F) :=
  (toAffineAll (windowBases (hintBase me z mask))).map fun vs => vs.flatMap fun v => [v.1, v.2]

/-- This party's torsion hint: `[1/8 mod ℓ]·Q` for its hinted point `Q`. -/
def torsionHint (me : Party) (z mask : Value) : Value := mul eighth (hintBase me z mask)

/-- The lift's public root (`LocalField::root`): for an opened nonzero `w`, whether it is a square
(`sel`), and `√(−486664)/s` for `s` a root of `w` (a square) or of `w/2` (not). -/
def root (w : F) : Option (Bool × F) :=
  let sel := euler w == ofNat 1
  match sqrt (if sel then w else w * inv (ofNat 2)) with
  | none => none
  | some s => some (sel, sA2 * inv s)

/-- **The root is a root**: the returned `s` satisfies `s² = w` (when `sel`) or `s² = w/2`. -/
theorem root_spec (w : F) (sel : Bool) (c : F) (h : root w = some (sel, c)) :
    ∃ s, s * s = (if sel then w else w * inverse (ofNat 2)) ∧ c = sA2 * inverse s := by
  unfold root at h
  dsimp only at h
  split at h
  · cases h
  · next s hs =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨s, ?_, by rw [inv_eq]⟩
    rw [sqrt_sq _ _ hs]
    split <;> simp [inv_eq]

/-- The table of a PUBLIC point (`Hinted::public_table`): `2^i·P` for `i < 256` as `x, y, 1, x·y`
(1024 elements); `none` only if a projective `Z` were zero. -/
def publicTable (p : Value) : Option (List F) :=
  let pts := ((List.range 256).foldl (fun (st : List ExtV × ExtV) _ =>
    (st.2 :: st.1, extAdd st.2 st.2)) ([], ofAffine p)).1.reverse
  (toAffineAll pts).map fun vs => vs.flatMap fun v => [v.1, v.2, ofNat 1, v.1 * v.2]

/-! ## XEdDSA key recovery on a public input (replaces `field_program.h` `evaluate_clear`) -/

/-- **`xeddsa-recover` evaluated in the clear** on a public Montgomery `u`: the Lean definition of the
program (`XEdDsaField.run concrete true`), run by each node locally; no rounds, nothing opened. -/
def recoverPublic (u : F) : List F := TlsMpc.Signal.XEdDsaField.run TlsMpc.X25519.concrete true (fun _ => u)

/-- **It is the program's value**: the expressions of `xeddsa-recover` (`EstablishField.recover`, the
declaration `FieldProgramsV3.find "xeddsa-recover"` exports) evaluated at the input `u`. With
`FieldProgramsV3.Decl.values`, it is what the V3 program outputs on `u`. -/
theorem recoverPublic_eq (u : F) :
    recoverPublic u = TlsMpc.EstablishField.recover.map (TlsMpc.FieldDag.Expr.eval (fun _ => u)) := by
  unfold recoverPublic TlsMpc.EstablishField.recover
  rw [TlsMpc.Signal.XEdDsaField.run_map (TlsMpc.X25519.evaluationHom (fun _ => u)) true TlsMpc.FieldDag.Expr.input]
  rfl

/-! ## Scalars -/

/-- Bit `i` of a little-endian byte string. -/
def bit (s : Bytes) (i : Nat) : Bool := (s.getD (i / 8) 0).toNat.testBit (i % 8)

/-- The value of a little-endian byte string. -/
def scalarOf (s : Bytes) : Nat := TlsMpc.Node.Engine.fromLE s

/-- Bits 3 … 253 of a clamped X25519 share (`Hinted::shared_bits`), 251 of them. -/
def agreementBits (share : Bytes) : List Bool := (List.range 251).map fun i => bit share (i + 3)

/-- The low 252 bits of a scalar (`OffsetAgreement::prepare`: `scalar[31] &= 15`). -/
def offsetBits (scalar : Bytes) : List Bool := (List.range 252).map fun i => bit scalar i

#print axioms add_eq
#print axioms toAffine_eq
#print axioms toAffineAll_spec
#print axioms root_spec
#print axioms recoverPublic_eq

end TlsMpc.Node.Local.Edwards
