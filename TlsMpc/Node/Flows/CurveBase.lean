import TlsMpc.Node.Flows.Inversion
import TlsMpc.Node.Local.Edwards

/-!
# The curve flows' shared parts: program names, blocks, the recoding, staged flows

REORGANIZATION_PLAN.md stage S11 (`Flows/Curve.lean` uses this). No I/O; no emitter imports this
module.

  * Program names and their V3 shapes (`shapeOf`: data inputs, masks, outputs, as the exported
    files declare them; the shell refuses another count, so a wrong entry fails closed).
  * `sharedBlock`: each party inputs `k` random elements (marked never) and the engine adds them;
    used for program MASKS (consumed by the `program` instruction, decision D14) and for the
    programs' uniform shared data inputs (the lift's `r`, the links' masks, `ρ`).
  * `recode`: the signed base-16 recoding of the offset (`edwards_points.h` `step`, `step_inputs`),
    the C++ rule line for line, as `proofs/` `TlsMpcProofs.Ed25519.recode` (the same equations;
    the Mathlib package's `recode_value`, `recode_bound`, `recode64_value`, `offsetSum_recoded`
    are about this function: see `Flows/CurveProofs.lean` for the main-package proofs).
  * `Staged`: a flow with a LOCAL step between two scripts (this party's own computation on its
    store, from its own secrets and the first script's public result: the hinted points' hints,
    the torsion hint). Scripts carry no private data (Engine.lean decision D1); the local step is
    where a node's own secret arithmetic happens, outside the engines, and it releases nothing.
  * `pointExchange`: commit-then-open of this party's public points (the split-ECDH share k·B,
    the K₀ halves), with the commitment frame of `split_ecdh.h` / `edwards_points.h`
    (`tag ‖ party ‖ nonce ‖ value`, `Engine.commitFrame`).
-/

namespace TlsMpc.Node.Flows.Curve

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts (seq seqs openThen frees)
open TlsMpc.Node.Flows.Run (openFieldThen sayThen isLocal)
open TlsMpc.FieldDag (F modulus ofNat)
open TlsMpc.Node.Local.Edwards (Value)

/-! ## Program names and shapes -/

def onCurveName : Bytes := ascii "edwards-on-curve"
def addUName : Bytes := ascii "edwards-add-u"
def x25519Name : Bytes := ascii "x25519-fast"
def prepareName : Bytes := ascii "edwards-prepare"
def offsetSumName : Bytes := ascii "edwards-offset-sum"
def liftOpenName : Bytes := ascii "lift-open"
def liftPointName : Bytes := ascii "lift-point"
def prepareHintedName : Bytes := ascii "edwards-prepare-hinted"
def offsetSumFastName : Bytes := ascii "edwards-offset-sum-fast"
def bitTableName : Bytes := ascii "edwards-bit-table"
def bitSumName : Bytes := ascii "edwards-bit-sum"
def affineBitSumName : Bytes := ascii "edwards-affine-bit-sum"
def signatureSumName : Bytes := ascii "edwards-signature-sum"
def torsionName : Bytes := ascii "edwards-torsion-hinted"

/-- The V3 shape of each curve program: data inputs, masks (`D` rows), outputs, public outputs.
Read off the validated compilations (`FieldProgramsV3.find`, computed once; the shell's `check`
refuses any other count, so an error here fails closed). -/
def shapeOf : String → Option (Nat × Nat × Nat × Nat)
  | "edwards-on-curve" => some (2, 0, 1, 1)
  | "edwards-add-u" => some (4, 0, 2, 0)
  | "x25519-fast" => some (257, 0, 2, 0)
  | "edwards-prepare" => some (506, 2031, 1531, 505)
  | "edwards-offset-sum" => some (194, 128, 1, 0)
  | "lift-open" => some (8, 0, 6, 5)
  | "lift-point" => some (9, 5, 5, 3)
  | "edwards-prepare-hinted" => some (884, 1150, 1656, 630)
  | "edwards-offset-sum-fast" => some (194, 0, 2, 0)
  | "edwards-bit-table" => some (380, 252, 1150, 126)
  | "edwards-bit-sum" => some (1261, 0, 2, 0)
  | "edwards-affine-bit-sum" => some (757, 0, 2, 0)
  | "edwards-signature-sum" => some (2546, 2, 2, 0)
  | "edwards-torsion-hinted" => some (7, 4, 2, 0)
  | "field-quotient" => some (2, 1, 2, 1)
  | _ => none

def masksOf (name : String) : Nat := ((shapeOf name).map (·.2.1)).getD 0

/-! ## Labels -/

/-- The commitment to this party's points: kind `commitment` (100). -/
def commitLabel : Label := Label.jointRandomCommitment

/-! ## Blocks -/

/-- `k` field handles from `f`. -/
def hs (f k : Nat) : List FieldH := (List.range k).map fun i => ⟨f + i⟩

def freeFs (l : List FieldH) : List Instr := l.map .freeField

/-- Shared random values: each party inputs `k` random elements from its store slot `slot`
(handles `f …` for A, `f + k …` for B, marked never), and their sums `f + 2k …` (never). -/
def sharedBlock (f k slot : Nat) : List Instr :=
  .fieldInput (hs f k) (hs (f + k) k) .elements false slot ::
    (List.range k).map fun i => .fieldAdd ⟨f + 2 * k + i⟩ ⟨f + i⟩ ⟨f + k + i⟩

/-- The sums of a `sharedBlock`. -/
def sharedOut (f k : Nat) : List FieldH := hs (f + 2 * k) k

/-- The contributions of a `sharedBlock` (freed after use). -/
def sharedIns (f k : Nat) : List FieldH := hs f (2 * k)

/-- The handles a `sharedBlock` takes. -/
def sharedSpan (k : Nat) : Nat := 3 * k

/-- Field publics for a list of constants, from `f`. -/
def publics (f : Nat) (vs : List F) : List Instr := vs.zipIdx.map fun e => .fieldPublic ⟨f + e.2⟩ e.1

/-! ## The masked quotient of many pairs (`x25519_fast.h` `evaluate_many`, `Hinted::quotients`)

`Inversion.quotientScript` for `n` pairs in one round: one `field-quotient` instruction with `n`
copies, one fresh mask each (each party's random contribution, slot `slot`, n elements), the zero
flags opened together. Handles from `f`: `sharedBlock` (3n), the quotients and flags (2n). -/

def quotOuts (f n : Nat) : List FieldH := hs (f + 3 * n) (2 * n)
def quotResult (f n j : Nat) : FieldH := ⟨f + 3 * n + 2 * j⟩
def quotFlag (f n j : Nat) : FieldH := ⟨f + 3 * n + 2 * j + 1⟩
def quotFlags (f n : Nat) : List FieldH := (List.range n).map (quotFlag f n)

def quotSpan (n : Nat) : Nat := 5 * n

def quotientMany (f slot : Nat) (pairs : List (FieldH × FieldH)) : Script (List (FieldH × Bool)) :=
  let n := pairs.length
  if n = 0 then .done [] else
  seqs (sharedBlock f n slot ++
    [.program Inversion.quotientName n (pairs.flatMap fun p => [p.1, p.2]) (sharedOut f n) (quotOuts f n)
      Label.maskedDenominator]) <|
  openFieldThen (quotFlags f n) Label.maskedDenominator fun fl =>
    if fl.length = n then
      seqs (freeFs (sharedIns f n) ++ freeFs (quotFlags f n))
        (.done ((List.range n).map fun j => (quotResult f n j, fl.getD j 0 == ofNat 1)))
    else .abort "reply shape"

/-! ## Commit-then-open of this party's points -/

/-- Exchange this party's `count` points (32-byte encodings, concatenated in the byte slot
`points`) by commit-then-open with nonce slot `nonce`: commitment (`commitment`), then opening
(`ownPublicPoint`); check the peer's opening against its commitment and that it differs from ours;
decode both parties' points, require every peer point valid, and return the sums `A_j + B_j`
(party order), each required valid. -/
def pointExchange (hash : Bytes → Bytes) (me : Party) (tag : Bytes) (nonce points count : Nat) :
    Script (List Value) := do
  let (c, c') ← Script.exchange 32 commitLabel (.commitment tag nonce points)
  let (o, o') ← Script.exchange (32 + 32 * count) Label.ownPublicPoint (.opening [nonce, points])
  Script.ensure (hash (commitFrame tag me.other (o'.take 32) (o'.drop 32)) == c' && c' != c)
    "point commitment"
  let mine := (List.range count).map fun j => TlsMpc.Node.Local.Edwards.decode (((o.drop 32).drop (32 * j)).take 32)
  let peer := (List.range count).map fun j => TlsMpc.Node.Local.Edwards.decode (((o'.drop 32).drop (32 * j)).take 32)
  match mine.mapM id, peer.mapM id with
  | some ms, some ps =>
    if ps.all TlsMpc.Node.Local.Edwards.isValid then
      let sums := (ms.zip ps).map fun e =>
        if me = .a then TlsMpc.Node.Local.Edwards.add e.1 e.2 else TlsMpc.Node.Local.Edwards.add e.2 e.1
      if sums.all TlsMpc.Node.Local.Edwards.isValid then pure sums else .abort "joint point"
    else .abort "peer point"
  | _, _ => .abort "point encoding"

/-! ## The signed base-16 recoding (`edwards_points.h` `step`, `step_inputs`) -/

/-- From carry `c`, the nibbles of `n` (least significant first) for `k` windows; the digits and the
final carry. Per window: `digit = nibble + carry; carry = digit > 8; digit −= 16·carry` (the C++
rule line for line; `proofs/` `TlsMpcProofs.Ed25519.recode` has the same equations). -/
def recode : Nat → Nat → Nat → List Int × Nat
  | c, _, 0 => ([], c)
  | c, n, k + 1 =>
    let carry := if 8 < n % 16 + c then 1 else 0
    let rest := recode carry (n / 16) k
    ((((n % 16 + c : Nat) : Int) - 16 * ((carry : Nat) : Int)) :: rest.1, rest.2)

/-- The value of base-16 digits, least significant first. -/
def digitsValue : List Int → Int
  | [] => 0
  | d :: rest => d + 16 * digitsValue rest

/-- The offset as the C++ uses it: 32 bytes, `offset[31] &= 15`: the value mod 2^252. -/
def offsetOf (bytes : Bytes) : Nat := TlsMpc.Node.Engine.fromLE bytes % 2 ^ 252

/-- The table index of window `w`'s digit `d ≠ 0` (`at = 2·(8w + |d| − 1)`): the x handle; y is
the next one. -/
def entryAt (w : Nat) (d : Int) : Nat := 2 * (8 * w + d.natAbs - 1)

/-- The window inputs of the offset sum (`step_inputs`): per window the table entry its digit
names and the sign (`1`, or `−1` for a negative digit), or the neutral element `(0, 1)` with sign
1 for a zero digit. `zero`, `one`, `minus` are handles holding the public constants. -/
def windowInputs (table : List FieldH) (zero one minus : FieldH) (digits : List Int) : List FieldH :=
  digits.zipIdx.flatMap fun e =>
    if e.1 = 0 then [zero, one, one]
    else [table.getD (entryAt e.2 e.1) zero, table.getD (entryAt e.2 e.1 + 1) zero, if 0 < e.1 then one else minus]

/-! ## Flows with a local step -/

/-- A flow with a local step between two scripts: the first script's (public) result `a`, then
this party's own computation on its store (`step a σ`: from its secrets and `a`; `none` aborts
locally, releasing nothing), then the second script. -/
structure Staged (α β : Type) where
  first : Script α
  step : α → Store → Option Store
  second : α → Script β

namespace Staged

/-- A run against an adversary: the first script's run, the local step on the store it left, then
the second script's run (the adversary's view carried over). -/
def withAdv (E : Env) (me : Party) (adv : Adversary) {α β : Type} (s : Staged α β) (σ : Store) (I : Ideal)
    (vD : List Release) : Outcome β :=
  let o := Engine.withAdv E me adv s.first σ I vD
  match o.result with
  | none => o.stop
  | some a =>
    match s.step a o.store with
    | none => o.stop
    | some σ' => o.then (Engine.withAdv E me adv (s.second a) σ' o.ideal (vD ++ o.viewD))

/-- Two honest parties: both first scripts, both local steps, both second scripts. -/
def jointRun (E : Env) {α β : Type} (sA sB : Staged α β) (σA σB : Store) (I : Ideal) : Outcome2 β β :=
  let o := Engine.jointRun E sA.first sB.first σA σB I
  match o.result with
  | none => ⟨none, o.storeA, o.storeB, o.ideal, o.viewA, o.viewB, o.trace⟩
  | some (a, b) =>
    match sA.step a o.storeA, sB.step b o.storeB with
    | some σA', some σB' =>
      let o₂ := Engine.jointRun E (sA.second a) (sB.second b) σA' σB' o.ideal
      ⟨o₂.result, o₂.storeA, o₂.storeB, o₂.ideal, o.viewA ++ o₂.viewA, o.viewB ++ o₂.viewB, o.trace ++ o₂.trace⟩
    | _, _ => ⟨none, o.storeA, o.storeB, o.ideal, o.viewA, o.viewB, o.trace⟩

end Staged

/-! ## Results of the hinted lift and the offset preparation -/

/-- A lifted point: its private validity bit and coordinates, the opened masked point
`Z = P + M_A + M_B`, and whether the Montgomery coordinate was 0 (`w` opened as 0). -/
structure Lifted where
  valid : FieldH
  x : FieldH
  y : FieldH
  z : Value
  zero : Bool

/-- A prepared offset agreement: the initial point `k₀·R` (two handles), the table (1024 handles:
entry `8w + (j − 1)` is `(j·16^w)·R`, x then y), and the public `K₀ = k₀·B`. -/
structure OffsetState where
  initial : FieldH × FieldH
  table : List FieldH
  key : Value

end TlsMpc.Node.Flows.Curve
