import TlsMpc.Node.Flows.CurveBase

/-!
# `Curve`: split ECDH, ladder agreements, the offset agreement, the hinted programs, op 66

REORGANIZATION_PLAN.md 7.1 (P-SPLIT, P-OFFSET, P-HINT), stage S11. The C++ of `split_ecdh.h`,
`x25519_fast.h`, `edwards_points.h`, `hinted_points.h` and `service_kernels.h` `prepare_hinted` /
`prepare_batch` (op 66) as Lean scripts on the engine instruction set (`program`, V3), the S10
conversions and masked inversion, and `Local/Edwards` for a node's own arithmetic in the clear.
No I/O; no emitter imports this module. Proofs: `Flows/CurveProofs.lean`.

THE FLOWS (handles: field ids from `f0`, fresh blocks; store slots named per flow; every program
mask is a `sharedBlock` sum consumed by its `program`):
  * `splitBegin` (split ECDH, key generation): commit-then-open of k·B (`pointExchange`, tag
    "split-ecdh-share"); the client's key share u(P_A + P_B) computed locally (`Local/Edwards`).
  * `splitAgree`: each party's T = k·S (computed locally by `splitAgreeInputs`, store slot) into the
    field engine; `edwards-on-curve` on both, the checks opened (`curveChecks`), must be 0;
    `edwards-add-u`; the masked quotient (`Inversion.quotientScript`).
  * `agree`: n X25519 agreements on shared swap bits: `x25519-fast` (n copies) and one masked
    quotient round (`quotientMany`).
  * `offsetPrepare` / `offsetStep` / `offsetStepFast` (`edwards_points.h`): the table program with
    both parties' scalar bits, its 505 checks opened; K₀ halves commit-then-open (tag
    "offset-agreement-K"); per message the offset's signed digits by `recode` IN LEAN (there is no
    C++ step), the ephemeral key u(K₀ + τ·B) locally, the sum program.
  * Hinted (`hinted_points.h`): `lift` (lift-open: the four checks opened first, then w; the public
    root locally; lift-point: Z opened), `hintsLocal` / `torsionLocal` (a party's own hints, the
    local step), `tables` (edwards-bit-table, links opened), `agreeHinted` / `agreeAffine`
    (bit sums + quotients), `signatures` (edwards-signature-sum), `torsion`
    (edwards-torsion-hinted), `sharedBits` (`Convert.sharedBits` on bits 3 … 253).
  * `prepareContacts` (op 66, `prepare_hinted`): a `Staged` flow: lift the recipients and open
    their validity bits (`pointValid`: the only place they are opened); the local step (hints,
    scalar bits, K₀ halves); `edwards-prepare-hinted` with its 630 checks opened (`linkChecks`);
    K₀ commit-then-open; the static agreements from the tables (`agreeAffine`).
-/

namespace TlsMpc.Node.Flows.Curve

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts (seq seqs openThen frees)
open TlsMpc.Node.Flows.Run (openFieldThen sayThen isLocal)
open TlsMpc.FieldDag (F modulus ofNat)
open TlsMpc.Node.Local.Edwards
open TlsMpc.Node.Local.Field (toBytes)

/-- All values zero. -/
def allZero (z : List F) : Bool := z.all (· == 0)

/-! ## Split ECDH (`split_ecdh.h`; P-SPLIT) -/

def splitTag : Bytes := ascii "split-ecdh-share"

/-- LOCAL (before `splitBegin`): this party's share k·B, encoded, for its byte slot. -/
def splitShare (k : Nat) : Option Bytes :=
  let p := mul k base
  if isNeutral p then none else some (encode p)

/-- **Split ECDH, key generation** (`SplitEcdh::begin`): the client's public key share
u(P_A + P_B), 32 bytes. `nonce`, `share`: byte slots (32 random bytes; `splitShare k`). -/
def splitBegin (hash : Bytes → Bytes) (me : Party) (nonce share : Nat) : Script Bytes :=
  (pointExchange hash me splitTag nonce share 1).bind fun sums =>
    match sums with
    | [s] => .done (toBytes (montU s))
    | _ => .abort "joint key share"

/-- LOCAL (before `splitAgree`): T = k·S for the server's public u (`LocalCurve.lift`, libsodium's
scalar multiplication), as `[x, y]`; `none` rejects the peer share publicly (both parties alike). -/
def splitAgreeInputs (k : Nat) (peerU : F) : Option (List F) :=
  match liftU peerU with
  | none => none
  | some s =>
    if isValid s then
      let t := mul k s
      if isNeutral t then none else some [t.1, t.2]
    else none

/-- The instructions before the curve checks are opened. -/
def splitBlock (f0 tSlot : Nat) : List Instr :=
  [.fieldInput (hs f0 2) (hs (f0 + 2) 2) .elements false tSlot, .fieldCheck,
   .program onCurveName 2 (hs f0 4) [] (hs (f0 + 4) 2) Label.curveChecks]

/-- The instructions after the checks passed. -/
def splitTail (f0 : Nat) : List Instr :=
  .program addUName 1 (hs f0 4) [] (hs (f0 + 6) 2) Label.curveChecks :: freeFs (hs f0 6)

/-- **Split ECDH, agreement** (`SplitEcdh::agree`): u((k_A + k_B)·S) as a private field element and
the zero flag. `tSlot`: this party's `[x, y]` of k·S; `maskSlot`: one random element. Handles
`f0 … f0 + 12`. -/
def splitAgree (f0 tSlot maskSlot : Nat) : Script (FieldH × Bool) :=
  seqs (splitBlock f0 tSlot) <|
  openFieldThen (hs (f0 + 4) 2) Label.curveChecks fun z =>
    if z.length = 2 ∧ allZero z = true then
      seqs (splitTail f0) (Inversion.quotientScript (f0 + 8) maskSlot ⟨f0 + 6⟩ ⟨f0 + 7⟩)
    else .abort "agreement share is not a curve point"

/-! ## X25519 on shared swap bits (`x25519_fast.h`) -/

/-- The 257 inputs of one `x25519-fast` instance: 0, 1, 254, 255 unused (zero), the 252 swap bits at
2 … 253, the point at 256 (`X25519Fast.swapInput`). -/
def ladderIns (zero : FieldH) (swaps : List FieldH) (u : FieldH) : List FieldH :=
  [zero, zero] ++ swaps ++ [zero, zero, u]

/-- **X25519 agreements** (`X25519Fast::evaluate_many`): per job its 252 swap-bit handles and the
point; the ladders in one program instruction, then one masked-quotient round. -/
def agree (f0 slot : Nat) (jobs : List (List FieldH × FieldH)) : Script (List (FieldH × Bool)) :=
  let n := jobs.length
  if n = 0 then .done [] else
  if jobs.all (fun j => j.1.length == 252) then
    seqs [.fieldPublic ⟨f0⟩ (ofNat 0),
      .program x25519Name n (jobs.flatMap fun j => ladderIns ⟨f0⟩ j.1 j.2) [] (hs (f0 + 1) (2 * n))
        Label.curveChecks, .freeField ⟨f0⟩] <|
    quotientMany (f0 + 1 + 2 * n) slot ((List.range n).map fun j => (⟨f0 + 1 + 2 * j⟩, ⟨f0 + 2 + 2 * j⟩))
  else .abort "swap bit count"

/-! ## The offset agreement (`edwards_points.h`; P-OFFSET) -/

def offsetTag : Bytes := ascii "offset-agreement-K"

/-- LOCAL: the scalar bits (`scalar[31] &= 15`, bits 0 … 251) as coins. -/
def offsetCoins (scalar : Bytes) : List F := (offsetBits scalar).map TlsMpc.X25519.bitValue

/-- LOCAL: this party's K₀ half k·B, encoded (k the scalar mod 2^252). -/
def offsetShare (scalar : Bytes) : Bytes := encode (mul (scalarOf scalar % 2 ^ 252) base)

/-- Store slots of `offsetPrepare`: `r` one random element; `bits` 252 coins (`offsetCoins`);
`masks` 2031 random elements; `nonce` 32 bytes; `share` (`offsetShare`). -/
structure OffsetSlots where
  r : Nat
  bits : Nat
  masks : Nat
  nonce : Nat
  share : Nat

def prepMasks : Nat := 2031

def prepBlock (f0 : Nat) (s : OffsetSlots) (u : FieldH) : List Instr :=
  let fb := f0 + 3
  let fm := fb + 504
  let fo := fm + 3 * prepMasks
  sharedBlock f0 1 s.r ++ [.fieldInput (hs fb 252) (hs (fb + 252) 252) .coins false s.bits, .fieldCheck] ++
    sharedBlock fm prepMasks s.masks ++
    [.program prepareName 1 (u :: sharedOut f0 1 ++ hs fb 504) (sharedOut fm prepMasks) (hs fo 1531)
      Label.maskedDenominator]

def prepOuts (f0 : Nat) : Nat := f0 + 3 + 504 + 3 * prepMasks

/-- **Offset agreement, preparation** (`OffsetAgreement::prepare`): the table program on the private
recipient `u`, its 505 checks opened (`curveChecks`, all zero), then K₀ by commit-then-open. -/
def offsetPrepare (hash : Bytes → Bytes) (me : Party) (f0 : Nat) (s : OffsetSlots) (u : FieldH) :
    Script OffsetState :=
  let fo := prepOuts f0
  seqs (prepBlock f0 s u) <|
  openFieldThen (hs fo 505) Label.curveChecks fun z =>
    if z.length = 505 ∧ allZero z = true then
      seqs (freeFs (sharedIns f0 1 ++ sharedOut f0 1 ++ hs (f0 + 3) 504 ++ sharedIns (f0 + 507) prepMasks ++ hs fo 505)) <|
      (pointExchange hash me offsetTag s.nonce s.share 1).bind fun keys =>
        match keys with
        | [k] => .done ⟨(⟨fo + 505⟩, ⟨fo + 506⟩), hs (fo + 507) 1024, k⟩
        | _ => .abort "initial public key"
    else .abort "offset agreement: invalid recipient key or scalar contribution"

/-- LOCAL (public): the ephemeral public key u(K₀ + τ·B), required a valid point. -/
def ephemeralKey (key : Value) (τ : Nat) : Option F :=
  let k := add key (mul τ base)
  if isValid k then some (montU k) else none

/-- The step's public constants 0, 1, −1 at `f0 … f0 + 2`. -/
def stepConsts (f0 : Nat) : List Instr := publics f0 [ofNat 0, ofNat 1, ofNat 0 - ofNat 1]

/-- **The inputs of the offset sum** (`step_inputs`): the initial point, then per window the entry
its digit (`recode 0 τ 64`) names and the sign. -/
def stepIns (f0 : Nat) (st : OffsetState) (τ : Nat) : List FieldH :=
  [st.initial.1, st.initial.2] ++ windowInputs st.table ⟨f0⟩ ⟨f0 + 1⟩ ⟨f0 + 2⟩ (recode 0 τ 64).1

/-- **Offset agreement, per message** (`OffsetAgreement::step`), with `edwards-offset-sum` (its
128 `D` rows' masks from `maskSlot`): the ephemeral key (public) and the private agreement u. -/
def offsetStep (f0 maskSlot : Nat) (st : OffsetState) (τ : Nat) : Script (F × FieldH) :=
  match ephemeralKey st.key τ with
  | none => .abort "ephemeral public key"
  | some u =>
    if (recode 0 τ 64).2 = 0 then
      seqs (stepConsts f0 ++ sharedBlock (f0 + 3) 128 maskSlot ++
        [.program offsetSumName 1 (stepIns f0 st τ) (sharedOut (f0 + 3) 128) [⟨f0 + 3 + 384⟩]
          Label.maskedDenominator] ++ freeFs (hs f0 3 ++ sharedIns (f0 + 3) 128))
        (.done (u, ⟨f0 + 387⟩))
    else .abort "offset recoding"

/-- The same with `edwards-offset-sum-fast` and one masked quotient (`Hinted::step`); a neutral sum
aborts. -/
def offsetStepFast (f0 slot : Nat) (st : OffsetState) (τ : Nat) : Script (F × FieldH) :=
  match ephemeralKey st.key τ with
  | none => .abort "ephemeral public key"
  | some u =>
    if (recode 0 τ 64).2 = 0 then
      seqs (stepConsts f0 ++ [.program offsetSumFastName 1 (stepIns f0 st τ) [] (hs (f0 + 3) 2) Label.curveChecks] ++
        freeFs (hs f0 3)) <|
      (quotientMany (f0 + 5) slot [(⟨f0 + 3⟩, ⟨f0 + 4⟩)]).bind fun r =>
        match r with
        | [(q, zero)] => if zero then .abort "offset agreement: neutral sum" else .done (u, q)
        | _ => .abort "reply shape"
    else .abort "offset recoding"

/-- The entries `2^i·R`, `i = 3 … 254`, of a prepared table (`OffsetAgreement::powers`). -/
def powers (st : OffsetState) : List FieldH :=
  (List.range' 3 252).flatMap fun i =>
    let idx := 2 * (8 * (i / 4) + 2 ^ (i % 4) - 1)
    [st.table.getD idx ⟨0⟩, st.table.getD (idx + 1) ⟨0⟩]

/-! ## The hinted lift (`Hinted::lift`; P-HINT) -/

/-- Store slots of `lift`: `coins` n random bits (0/1); `points` this party's mask points `x, y`
(2n, `randomPoint`); `r` n random elements; `masks` 5n random elements. -/
structure LiftSlots where
  coins : Nat
  points : Nat
  r : Nat
  masks : Nat

section LiftLayout
variable (f0 n : Nat)
def lfc : Nat := f0
def lfp : Nat := f0 + 2 * n
def lfr : Nat := lfp f0 n + 4 * n
def lfo : Nat := lfr f0 n + 3 * n
def lfk : Nat := lfo f0 n + 6 * n
def lfm : Nat := lfk f0 n + 3 * n
def lfl : Nat := lfm f0 n + 15 * n
def liftSpan : Nat := 38 * n
end LiftLayout

/-- Instance `j` of `lift-open`: u, r, the two bits, A's mask point, B's mask point. -/
def openIns (f0 n : Nat) (us : List FieldH) (j : Nat) : List FieldH :=
  [us.getD j ⟨0⟩, ⟨lfr f0 n + 2 * n + j⟩, ⟨lfc f0 + j⟩, ⟨lfc f0 + n + j⟩,
   ⟨lfp f0 n + 2 * j⟩, ⟨lfp f0 n + 2 * j + 1⟩, ⟨lfp f0 n + 2 * n + 2 * j⟩, ⟨lfp f0 n + 2 * n + 2 * j + 1⟩]

def liftBlock (f0 : Nat) (s : LiftSlots) (us : List FieldH) : List Instr :=
  let n := us.length
  [.fieldInput (hs (lfc f0) n) (hs (lfc f0 + n) n) .coins false s.coins,
   .fieldInput (hs (lfp f0 n) (2 * n)) (hs (lfp f0 n + 2 * n) (2 * n)) .elements false s.points] ++
  sharedBlock (lfr f0 n) n s.r ++
  [.fieldCheck,
   .program liftOpenName n ((List.range n).flatMap (openIns f0 n us)) [] (hs (lfo f0 n) (6 * n)) Label.curveChecks]

/-- The four checks of every instance (opened first). -/
def liftChecks (f0 n : Nat) : List FieldH :=
  (List.range n).flatMap fun j => hs (lfo f0 n + 6 * j + 1) 4

/-- Every instance's `w` (opened after the checks). -/
def liftWs (f0 n : Nat) : List FieldH := (List.range n).map fun j => ⟨lfo f0 n + 6 * j⟩

/-- The public roots of the opened `w`s: `(cs, sel, zero)` per instance (`w = 0`: `u = 0`). -/
def roots (ws : List F) : Option (List (F × F × Bool)) :=
  ws.mapM fun w =>
    if w = 0 then some (ofNat 0, ofNat 0, true)
    else (root w).map fun r => (r.2, if r.1 then ofNat 1 else ofNat 0, false)

/-- Instance `j` of `lift-point`: cs, sel, u, r, b (0 when `w = 0`), the two mask points. -/
def pointIns (f0 n : Nat) (us : List FieldH) (rs : List (F × F × Bool)) (j : Nat) : List FieldH :=
  [⟨lfk f0 n + 3 * j⟩, ⟨lfk f0 n + 3 * j + 1⟩, us.getD j ⟨0⟩, ⟨lfr f0 n + 2 * n + j⟩,
   if (rs.getD j (0, 0, false)).2.2 then ⟨lfk f0 n + 3 * j + 2⟩ else ⟨lfo f0 n + 6 * j + 5⟩,
   ⟨lfp f0 n + 2 * j⟩, ⟨lfp f0 n + 2 * j + 1⟩, ⟨lfp f0 n + 2 * n + 2 * j⟩, ⟨lfp f0 n + 2 * n + 2 * j + 1⟩]

def pointBlock (f0 : Nat) (s : LiftSlots) (us : List FieldH) (rs : List (F × F × Bool)) : List Instr :=
  let n := us.length
  publics (lfk f0 n) (rs.flatMap fun r => [r.1, r.2.1, ofNat 0]) ++ sharedBlock (lfm f0 n) (5 * n) s.masks ++
  [.program liftPointName n ((List.range n).flatMap (pointIns f0 n us rs)) (sharedOut (lfm f0 n) (5 * n))
    (hs (lfl f0 n) (5 * n)) Label.maskedDenominator]

def liftZs (f0 n : Nat) : List FieldH := (List.range n).flatMap fun j => hs (lfl f0 n + 5 * j + 3) 2

/-- The handles freed at the end of the lift (everything but valid, x, y). -/
def liftFrees (f0 n : Nat) : List Instr :=
  freeFs (hs (lfc f0) (2 * n) ++ hs (lfp f0 n) (4 * n) ++ sharedIns (lfr f0 n) n ++ sharedOut (lfr f0 n) n ++
    hs (lfo f0 n) (6 * n) ++ hs (lfk f0 n) (3 * n) ++ sharedIns (lfm f0 n) (5 * n) ++ liftZs f0 n)

def liftResult (f0 n : Nat) (zv : List F) (rs : List (F × F × Bool)) : List Lifted :=
  (List.range n).map fun j =>
    ⟨⟨lfl f0 n + 5 * j⟩, ⟨lfl f0 n + 5 * j + 1⟩, ⟨lfl f0 n + 5 * j + 2⟩,
     (zv.getD (2 * j) 0, zv.getD (2 * j + 1) 0), (rs.getD j (0, 0, false)).2.2⟩

/-- **The hinted lift** (`Hinted::lift`) of the Montgomery coordinates `us` (private handles).
Opened, in this order: the 4n checks (`curveChecks`, must be 0), the n values `w` (`liftW`), the
lift-point openings (`maskedDenominator`), the n masked points `Z` (`liftZ`, must be curve points).
Handles `f0 …` (`liftSpan n`). -/
def lift (f0 : Nat) (s : LiftSlots) (us : List FieldH) : Script (List Lifted) :=
  let n := us.length
  if n = 0 then .done [] else
  seqs (liftBlock f0 s us) <|
  openFieldThen (liftChecks f0 n) Label.curveChecks fun z =>
  if z.length = 4 * n ∧ allZero z = true then
    openFieldThen (liftWs f0 n) Label.liftW fun ws =>
    if ws.length = n then
      match roots ws with
      | none => .abort "lift root"
      | some rs =>
        seqs (pointBlock f0 s us rs) <|
        openFieldThen (liftZs f0 n) Label.liftZ fun zv =>
        if zv.length = 2 * n ∧ (liftResult f0 n zv rs).all (fun l => onCurve l.z) then
          seqs (liftFrees f0 n) (.done (liftResult f0 n zv rs))
        else .abort "hinted lift: Z is not a curve point"
    else .abort "reply shape"
  else .abort "hinted lift: a mask contribution is not a bit or not a curve point"

/-- LOCAL (before `lift`): a party's coins and mask points from its randomness (`randomPoint`). -/
def liftLocalInputs (rnd : List (Nat × Nat × Bool)) : List F × List F :=
  (rnd.map fun e => TlsMpc.X25519.bitValue e.2.2,
   rnd.flatMap fun e => let p := randomPoint e.1 e.2.1; [p.1, p.2])

/-! ## Hints (the local step) and tables -/

/-- LOCAL: this party's hints (126 elements per point) for the lifted points `ls` (with their
index in the lift, for the mask point in slot `points`), into slot `out`. -/
def hintsLocal (me : Party) (points out : Nat) (ls : List (Lifted × Nat)) (σ : Store) : Option Store :=
  let pts := σ.elems points
  (ls.mapM fun e => hints me e.1.z (pts.getD (2 * e.2) 0, pts.getD (2 * e.2 + 1) 0)).map fun l =>
    σ.setElems out l.flatten

/-- The 252 hint inputs of point `j` of `m` (`fh`: A's 126m then B's 126m): per window A's x, y then
B's x, y. -/
def hintRow (fh m j : Nat) : List FieldH :=
  (List.range 63).flatMap fun w =>
    [⟨fh + 126 * j + 2 * w⟩, ⟨fh + 126 * j + 2 * w + 1⟩, ⟨fh + 126 * m + 126 * j + 2 * w⟩, ⟨fh + 126 * m + 126 * j + 2 * w + 1⟩]

def hintInput (fh m slot : Nat) : Instr := .fieldInput (hs fh (126 * m)) (hs (fh + 126 * m) (126 * m)) .elements false slot

/-- Store slots of `tables`: `hints` 126m (`hintsLocal`); `links` 126m random; `masks` 252m random. -/
structure TableSlots where
  hints : Nat
  links : Nat
  masks : Nat

def tableSpan (m : Nat) : Nat := 2536 * m

/-- **Bit tables** (`Hinted::tables`): `2^i·P` for every lifted point, the 126 masked links per point
opened (`linkChecks`, all zero). Returns 1024 handles per point (x, y, z, t per entry). -/
def tables (f0 : Nat) (s : TableSlots) (pts : List Lifted) : Script (List (List FieldH)) :=
  let m := pts.length
  let fl := f0 + 252 * m
  let fm := fl + 378 * m
  let fo := fm + 756 * m
  if m = 0 then .done [] else
  seqs ([hintInput f0 m s.hints] ++ sharedBlock fl (126 * m) s.links ++ sharedBlock fm (252 * m) s.masks ++ [.fieldCheck,
    .program bitTableName m ((pts.zipIdx).flatMap fun e =>
        [e.1.x, e.1.y] ++ hintRow f0 m e.2 ++ ((sharedOut fl (126 * m)).drop (126 * e.2)).take 126)
      (sharedOut fm (252 * m)) (hs fo (1150 * m)) Label.maskedDenominator]) <|
  openFieldThen ((List.range m).flatMap fun j => hs (fo + 1150 * j) 126) Label.linkChecks fun z =>
    if z.length = 126 * m ∧ allZero z = true then
      seqs (freeFs (hs f0 (252 * m) ++ sharedIns fl (126 * m) ++ sharedOut fl (126 * m) ++ sharedIns fm (252 * m) ++
          (List.range m).flatMap fun j => hs (fo + 1150 * j) 126))
        (.done ((List.range m).map fun j => hs (fo + 1150 * j + 126) 1024))
    else .abort "bit table: a hint is wrong"

/-! ## Agreements from tables (`Hinted::agree`, `agree_affine`) -/

/-- An agreement job: 251 scalar-bit handles (bits 3 … 253), the point's table (none: its
coordinate was 0, the result is 0), and its validity handle. -/
structure HintedJob where
  bits : List FieldH
  table : Option (List FieldH)
  valid : FieldH

/-- **X25519 from bit tables**: `edwards-bit-sum` on the live jobs (ρ from `rho`), then one masked
quotient round (`qslot`); a job without a table gives the constant 0 and `zero = true`. -/
def agreeHinted (f0 rho qslot : Nat) (jobs : List HintedJob) : Script (List (FieldH × Bool)) :=
  let live := jobs.filterMap fun j => j.table.map fun t => (j, t)
  let m := live.length
  let fo := f0 + 1 + 3 * m
  let assemble (us : List (FieldH × Bool)) : List (FieldH × Bool) :=
    (jobs.foldl (fun (st : List (FieldH × Bool) × Nat) j =>
      match j.table with
      | some _ => (st.1 ++ [us.getD st.2 (⟨f0⟩, true)], st.2 + 1)
      | none => (st.1 ++ [(⟨f0⟩, true)], st.2)) ([], 0)).1
  if live.all (fun e => e.1.bits.length == 251 && e.2.length == 1024) then
    seqs [.fieldPublic ⟨f0⟩ (ofNat 0)] <|
    if m = 0 then .done (assemble []) else
    seqs (sharedBlock (f0 + 1) m rho ++
      [.program bitSumName m ((live.zipIdx).flatMap fun e =>
          [e.1.1.valid, ⟨f0 + 1 + 2 * m + e.2⟩] ++ (e.1.2.drop 12).take 1008 ++ e.1.1.bits) [] (hs fo (2 * m))
        Label.curveChecks] ++ freeFs (sharedIns (f0 + 1) m ++ sharedOut (f0 + 1) m)) <|
    (quotientMany (fo + 2 * m) qslot ((List.range m).map fun j => (⟨fo + 2 * j⟩, ⟨fo + 2 * j + 1⟩))).bind fun us =>
      .done (assemble us)
  else .abort "agreement job shape"

/-- **X25519 from affine powers** (`agree_affine`, points known valid): per job 251 bits and the 252
affine points `2^i·P` (`powers`), `edwards-affine-bit-sum`, one quotient round. -/
def agreeAffine (f0 rho qslot : Nat) (jobs : List (List FieldH × List FieldH)) : Script (List (FieldH × Bool)) :=
  let m := jobs.length
  let fo := f0 + 1 + 3 * m
  if m = 0 then .done [] else
  if jobs.all (fun j => j.1.length == 251 && j.2.length == 504) then
    seqs ([.fieldPublic ⟨f0⟩ (ofNat 1)] ++ sharedBlock (f0 + 1) m rho ++
      [.program affineBitSumName m ((jobs.zipIdx).flatMap fun e =>
          [⟨f0⟩, ⟨f0 + 1 + 2 * m + e.2⟩] ++ e.1.2 ++ e.1.1) [] (hs fo (2 * m)) Label.curveChecks] ++
      freeFs (⟨f0⟩ :: sharedIns (f0 + 1) m ++ sharedOut (f0 + 1) m)) <|
    quotientMany (fo + 2 * m) qslot ((List.range m).map fun j => (⟨fo + 2 * j⟩, ⟨fo + 2 * j + 1⟩))
  else .abort "agreement job shape"

/-! ## Signatures, torsion, shared bits -/

/-- The public table of B (`Hinted::base_table`): 1024 constants from `f0`. -/
def baseTableBlock (f0 : Nat) : List Instr := publics f0 ((publicTable base).getD [])

/-- **XEdDSA verification points** `[s]B − [h]A` (`Hinted::signatures`): per job the key's table
(1024 handles) and `flip, h (256 bits), s (253 bits)`; `baseT` the base table (`baseTableBlock`).
Two `D` masks per job from `maskSlot`. -/
def signatures (f0 maskSlot : Nat) (baseT : List FieldH) (jobs : List (List FieldH × List FieldH)) :
    Script (List (FieldH × FieldH)) :=
  let n := jobs.length
  let fo := f0 + 6 * n
  if n = 0 then .done [] else
  if jobs.all (fun j => j.1.length == 1024 && j.2.length == 510) && baseT.length == 1024 then
    seqs (sharedBlock f0 (2 * n) maskSlot ++
      [.program signatureSumName n (jobs.flatMap fun j =>
          j.2.take 1 ++ j.1 ++ (j.2.drop 1).take 256 ++ baseT.take 1012 ++ j.2.drop 257)
        (sharedOut f0 (2 * n)) (hs fo (2 * n)) Label.maskedDenominator] ++ freeFs (sharedIns f0 (2 * n)))
      (.done ((List.range n).map fun j => (⟨fo + 2 * j⟩, ⟨fo + 2 * j + 1⟩)))
  else .abort "signature job shape"

/-- LOCAL: this party's torsion hints `[1/8]·Q` (x, y per point) into slot `out`. -/
def torsionLocal (me : Party) (points out : Nat) (ls : List (Lifted × Nat)) (σ : Store) : Option Store :=
  let pts := σ.elems points
  some (σ.setElems out (ls.flatMap fun e =>
    let q := torsionHint me e.1.z (pts.getD (2 * e.2) 0, pts.getD (2 * e.2 + 1) 0)
    [q.1, q.2]))

/-- **Torsion checks** (`Hinted::torsion`): two private values per point, zero exactly for the
prime-order subgroup. Nothing is opened but the `D` openings. Slots: `hints` 2n (`torsionLocal`),
`r` n random, `masks` 4n random. -/
def torsion (f0 hintSlot rSlot maskSlot : Nat) (pts : List Lifted) : Script (List (FieldH × FieldH)) :=
  let n := pts.length
  let fr := f0 + 4 * n
  let fm := fr + 3 * n
  let fo := fm + 12 * n
  if n = 0 then .done [] else
  seqs ([.fieldInput (hs f0 (2 * n)) (hs (f0 + 2 * n) (2 * n)) .elements false hintSlot] ++
    sharedBlock fr n rSlot ++ sharedBlock fm (4 * n) maskSlot ++ [.fieldCheck,
    .program torsionName n ((pts.zipIdx).flatMap fun e =>
        [e.1.x, e.1.y, ⟨f0 + 2 * e.2⟩, ⟨f0 + 2 * e.2 + 1⟩, ⟨f0 + 2 * n + 2 * e.2⟩, ⟨f0 + 2 * n + 2 * e.2 + 1⟩,
         ⟨fr + 2 * n + e.2⟩])
      (sharedOut fm (4 * n)) (hs fo (2 * n)) Label.maskedDenominator] ++
    freeFs (hs f0 (4 * n) ++ sharedIns fr n ++ sharedOut fr n ++ sharedIns fm (4 * n)))
    (.done ((List.range n).map fun j => (⟨fo + 2 * j⟩, ⟨fo + 2 * j + 1⟩)))

/-- LOCAL: a share's bits 3 … 253 as coins (`Hinted::shared_bits`). -/
def shareCoins (share : Bytes) : List F := (agreementBits share).map TlsMpc.X25519.bitValue

/-- **Scalars as field bits** (`Hinted::shared_bits`): `Convert.sharedBits` on 251 bits. -/
def sharedBits (f0 slot : Nat) : Script (List FieldH) := Convert.sharedBits f0 251 slot

/-- A scalar both parties know, as constants (`Hinted::public_bits`). -/
def publicBits (f0 : Nat) (scalar : Bytes) : List Instr := publics f0 (shareCoins scalar)

/-! ## Contact preparation (op 66; `prepare_hinted`, `Hinted::prepare`) -/

/-- **First script**: lift the recipients, then open their validity bits (`pointValid`; each must be
0 or 1). Returns the lifted points and, per point, whether it is prepared further (valid, `u ≠ 0`). -/
def prepareFirst (f0 : Nat) (s : LiftSlots) (us : List FieldH) : Script (List Lifted × List Bool) :=
  (lift f0 s us).bind fun ls =>
    if ls.length = 0 then .done ([], []) else
    openFieldThen (ls.map (·.valid)) Label.pointValid fun v =>
      if v.length = ls.length ∧ v.all (fun x => x == 0 || x == ofNat 1) then
        .done (ls, (ls.zip v).map fun e => e.2 == ofNat 1 && !e.1.zero)
      else .abort "lift validity"

/-- Store slots of the preparation's second part. `scalars`: 32 random bytes per recipient (bytes
slot); `linkPool` / `maskPool`: random elements, at least 126 / 1150 per recipient; the slots
`hints`, `links`, `masks`, `bits` (elements) and `shares` (bytes) are written by the local step;
`nonce` 32 random bytes; `rho`, `qslot`: the agreement's random elements (one per prepared point). -/
structure PrepareSlots where
  lift : LiftSlots
  scalars : Nat
  linkPool : Nat
  maskPool : Nat
  hints : Nat
  links : Nat
  masks : Nat
  bits : Nat
  shares : Nat
  nonce : Nat
  rho : Nat
  qslot : Nat

/-- The prepared points (with their index in the lift). -/
def livePoints (r : List Lifted × List Bool) : List (Lifted × Nat) :=
  ((r.1.zip r.2).zipIdx).filterMap fun e => if e.1.2 then some (e.1.1, e.2) else none

/-- **The local step**: the hints of the prepared points, their scalars' bits (coins) and K₀ halves,
and the random slots cut to size. Reads only this party's store. -/
def prepareLocal (me : Party) (s : PrepareSlots) (r : List Lifted × List Bool) (σ : Store) : Option Store :=
  let live := livePoints r
  let m := live.length
  let sc := (List.range m).map fun j => ((σ.bytes s.scalars).drop (32 * (live.getD j (⟨⟨0⟩, ⟨0⟩, ⟨0⟩, neutral, true⟩, 0)).2)).take 32
  match hintsLocal me s.lift.points s.hints live σ with
  | none => none
  | some σ1 =>
    let σ2 := σ1.setElems s.links ((σ.elems s.linkPool).take (126 * m))
    let σ3 := σ2.setElems s.masks ((σ.elems s.maskPool).take (1150 * m))
    let σ4 := σ3.setElems s.bits (sc.flatMap offsetCoins)
    some (σ4.setBytes s.shares (sc.flatMap offsetShare))

def hintedMasks : Nat := 1150

/-- **Second script**: `edwards-prepare-hinted` on the prepared points (both parties' scalar bits as
coins), its 630 checks per point opened (`linkChecks`: bit checks and links, all zero), K₀ by
commit-then-open (tag "offset-agreement-K", one exchange for the batch). -/
def prepareSecond (hash : Bytes → Bytes) (me : Party) (f0 : Nat) (s : PrepareSlots) (live : List Lifted) :
    Script (List OffsetState) :=
  let m := live.length
  let fl := f0 + 252 * m
  let fm := fl + 378 * m
  let fb := fm + 3 * hintedMasks * m
  let fo := fb + 504 * m
  if m = 0 then .done [] else
  seqs ([hintInput f0 m s.hints] ++ sharedBlock fl (126 * m) s.links ++ sharedBlock fm (hintedMasks * m) s.masks ++
    [.fieldInput (hs fb (252 * m)) (hs (fb + 252 * m) (252 * m)) .coins false s.bits, .fieldCheck,
     .program prepareHintedName m ((live.zipIdx).flatMap fun e =>
        [e.1.x, e.1.y] ++ hintRow f0 m e.2 ++ ((sharedOut fl (126 * m)).drop (126 * e.2)).take 126 ++
          hs (fb + 252 * e.2) 252 ++ hs (fb + 252 * m + 252 * e.2) 252)
      (sharedOut fm (hintedMasks * m)) (hs fo (1656 * m)) Label.maskedDenominator]) <|
  openFieldThen ((List.range m).flatMap fun j => hs (fo + 1656 * j) 630) Label.linkChecks fun z =>
    if z.length = 630 * m ∧ allZero z = true then
      seqs (freeFs (hs f0 (252 * m) ++ sharedIns fl (126 * m) ++ sharedOut fl (126 * m) ++
          sharedIns fm (hintedMasks * m) ++ hs fb (504 * m) ++ (List.range m).flatMap fun j => hs (fo + 1656 * j) 630)) <|
      (pointExchange hash me offsetTag s.nonce s.shares m).bind fun keys =>
        if keys.length = m then
          .done ((List.range m).map fun j =>
            ⟨(⟨fo + 1656 * j + 630⟩, ⟨fo + 1656 * j + 631⟩), hs (fo + 1656 * j + 632) 1024,
             keys.getD j neutral⟩)
        else .abort "initial public key"
    else .abort "offset agreement: a scalar contribution is not a bit or a hint is wrong"

/-- The handles the second script and the agreement take. -/
def prepareSpan (m : Nat) : Nat := (252 + 378 + 3 * hintedMasks + 504 + 1656) * m

/-- Op 66's reply: per recipient 255 (prepared) or 0 (its key is not a curve point, or `u = 0`). -/
def statusBytes (live : List Bool) : Bytes := live.map fun b => if b then 255 else 0

/-- **Op 66, `Curve.prepareContacts`** (`prepare_batch` with `hinted`): for the recipients' private
Montgomery coordinates `us` (the contacts' keys, converted to field elements by the caller) and the
account's identity-key bits (251 handles, bits 3 … 253), the status bytes, each prepared contact's
offset state and its static agreement u(k_identity · R) (private). Handles from `f0`: the lift
(`liftSpan n`), then the second part. -/
def prepareContacts (hash : Bytes → Bytes) (me : Party) (f0 : Nat) (s : PrepareSlots) (us : List FieldH)
    (identityBits : List FieldH) : Staged (List Lifted × List Bool) (Bytes × List (OffsetState × FieldH)) where
  first := prepareFirst f0 s.lift us
  step := prepareLocal me s
  second := fun r =>
    let live := (livePoints r).map (·.1)
    let f1 := f0 + liftSpan us.length
    (prepareSecond hash me f1 s live).bind fun sts =>
      (agreeAffine (f1 + prepareSpan live.length) s.rho s.qslot (sts.map fun st => (identityBits, powers st))).bind
        fun ags => .done (statusBytes r.2, sts.zip (ags.map (·.1)))

end TlsMpc.Node.Flows.Curve
