import TlsMpc.Node.Flows.Curve
import TlsMpc.FieldProgramsV3
import TlsMpc.Sha256

/-!
Test vectors of the S11 curve flows (`TlsMpc/Node/Flows/Curve.lean`) for the stand-in two-party
test `node_worker/tests/s11_pair.rs`, computed by the Lean model itself (Engine/Model.lean
`runWires` on each agreed batch) from the Lean scripts and the REAL field programs (each the
validated compilation of its declaration, `FieldProgramsV3.find`, as the emitter's `v3 NAME` prints
it; `field-quotient` is `FieldDagV3.quotient`). Not part of the library; nothing imports it.

    lake env lean --tstack=2000000 --run node_worker/tests/lean/S11Vectors.lean   # → tests/s11_vectors.txt

Format as `S10Vectors.lean` (`prog`, `flow … endflow`, `round`, `party`, `batch`, `verdict`,
`reply`, `finished | abort P REASON | error …`, `check NAME ok|FAIL`), plus `pin NAME SHA256` (the
SHA-256 of each V3 text: the pins the re-export must reproduce) and `local P …` lines that mark the
local step of a staged flow (between two scripts; nothing is sent).

SCENARIOS (plan 10.1 set E, `rounds_fixture` ported to scripts): split ECDH (key share and
agreement); nine X25519 agreements on shared swap bits; the offset agreement (prepare, a step with
`edwards-offset-sum`, a step with `edwards-offset-sum-fast`); the hinted programs (a lift of three
points, the local hints, bit tables, three agreements of which one has no table, a signature
point, torsion checks); op 66 on four contacts with an invalid key in the batch; and cheating
cases (party B deviates): an off-curve agreement share, an off-curve mask point, a wrong hint, a
wrong K₀ opening.
-/

open TlsMpc.Node.Engine
open TlsMpc.FieldDag (F modulus ofNat)
open TlsMpc.FieldDag.V3 (Program)
open TlsMpc.Node.Flows.Curve
open TlsMpc.Node.Local.Edwards
open TlsMpc.Node.Local.Field (toBytes)

namespace S11V

def digit (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'
def hexByte (b : UInt8) : String := String.ofList [digit (b.toNat / 16), digit (b.toNat % 16)]
def hex (bs : Bytes) : String := String.join (bs.map hexByte)

def sha256 (m : Bytes) : Bytes :=
  (TlsMpc.Sha256.hash TlsMpc.Sha256.concrete (m.map fun b => BitVec.ofNat 8 b.toNat)).map
    fun b => UInt8.ofNat b.toNat

def fe (n : Nat) : F := ofNat n

/-! ## The programs -/

def progNames : List String :=
  ["field-quotient", "field-bit-check", "field-bit-xor", "edwards-on-curve", "edwards-add-u", "x25519-fast",
   "edwards-prepare", "edwards-offset-sum", "lift-open", "lift-point", "edwards-prepare-hinted",
   "edwards-offset-sum-fast", "edwards-bit-table", "edwards-bit-sum", "edwards-affine-bit-sum",
   "edwards-signature-sum", "edwards-torsion-hinted"]

def compileOne (n : String) : Option Program :=
  if n = "field-quotient" then some TlsMpc.FieldDag.V3.quotient
  else (TlsMpc.FieldProgramsV3.find n).bind (·.program)

def mkEnv (table : List (String × Program)) : Env :=
  { circuits := fun _ => none, hash := sha256,
    programs := fun n => (table.find? (fun e => ascii e.1 == n)).map (·.2) }

/-! ## Two parties, batch by batch (as `S10Vectors.runPair`, contexts returned) -/

def emitBatch (E : Env) (c : Ctx) (b : List Wire) : Ctx × List String :=
  let lines := [s!"batch {hex (encodeBatch b)}"]
  match checkBatch E.sigs c (b.map InstrP.skel) with
  | .ok (c', _) => (c', lines ++ ["verdict ok"])
  | .error i => (c, lines ++ [s!"verdict refused {i}"])

structure Run (α : Type) where
  lines : List String
  result : Option (α × α)
  storeA : Store
  storeB : Store
  ideal : Ideal
  ctxA : Ctx
  ctxB : Ctx

def runPair (E : Env) {α : Type} : Nat → Script α → Script α → Store → Store → Ctx → Ctx → Ideal → List String → Run α
  | 0, _, _, σA, σB, ca, cb, I, acc => ⟨acc ++ ["error fuel"], none, σA, σB, I, ca, cb⟩
  | fuel + 1, sa, sb, σA, σB, ca, cb, I, acc =>
    let ba := nextBatch sha256 .a σA sa
    let bb := nextBatch sha256 .b σB sb
    match ba.rest, bb.rest with
    | .aborted r, _ => ⟨acc ++ [s!"abort a {r}"], none, σA, σB, I, ca, cb⟩
    | _, .aborted r => ⟨acc ++ [s!"abort b {r}"], none, σA, σB, I, ca, cb⟩
    | ra0, rb0 =>
      if ba.wires.isEmpty && bb.wires.isEmpty then
        match ra0, rb0 with
        | .finished x, .finished y => ⟨acc ++ ["finished"], some (x, y), σA, σB, I, ca, cb⟩
        | _, _ => ⟨acc ++ ["error shape"], none, σA, σB, I, ca, cb⟩
      else
        match runWires E ba.wires bb.wires I with
        | none => ⟨acc ++ ["error functionality"], none, σA, σB, I, ca, cb⟩
        | some (I', relA, relB) =>
          let ea := emitBatch E ca ba.wires
          let eb := emitBatch E cb bb.wires
          let lines := ["round", "party a"] ++ ea.2 ++ [s!"reply {hex (encodeReplies (relA.map (·.datum)))}"] ++
            ["party b"] ++ eb.2 ++ [s!"reply {hex (encodeReplies (relB.map (·.datum)))}"]
          match ra0, rb0 with
          | .finished x, .finished y => ⟨acc ++ lines ++ ["finished"], some (x, y), σA, σB, I', ea.1, eb.1⟩
          | .waiting ia ka, .waiting ib kb =>
            let rA := absorb sha256 .a ia σA (if ia.releasesTo .a then relA.getLast? else none)
            let rB := absorb sha256 .b ib σB (if ib.releasesTo .b then relB.getLast? else none)
            runPair E fuel (ka rA.1) (kb rB.1) rA.2 rB.2 ea.1 eb.1 I' (acc ++ lines)
          | _, _ => ⟨acc ++ lines ++ ["error shape"], none, σA, σB, I', ea.1, eb.1⟩

def fuel : Nat := 100

/-- A staged flow: the first scripts, the local steps (marked), the second scripts. -/
def runStaged (E : Env) {α β : Type} (sA sB : Staged α β) (σA σB : Store) (c : Ctx) (I : Ideal) : Run β :=
  let r := runPair E fuel sA.first sB.first σA σB c c I []
  match r.result with
  | none => ⟨r.lines, none, r.storeA, r.storeB, r.ideal, r.ctxA, r.ctxB⟩
  | some (a, b) =>
    match sA.step a r.storeA, sB.step b r.storeB with
    | some σA', some σB' =>
      let r2 := runPair E fuel (sA.second a) (sB.second b) σA' σB' r.ctxA r.ctxB r.ideal (r.lines ++ ["local a", "local b"])
      ⟨r2.lines, r2.result, r2.storeA, r2.storeB, r2.ideal, r2.ctxA, r2.ctxB⟩
    | _, _ => ⟨r.lines ++ ["abort a local step"], none, r.storeA, r.storeB, r.ideal, r.ctxA, r.ctxB⟩

def check (name : String) (ok : Bool) : String := s!"check {name} {if ok then "ok" else "FAIL"}"

/-! ## Stores and inputs -/

def mkStore (elems : List (Nat × List F)) (bytes : List (Nat × Bytes)) : Store :=
  { elems := fun j => (elems.lookup j).getD [], bytes := fun j => (bytes.lookup j).getD [] }

def P : Nat := modulus

/-- Deterministic "random" values per party `s`, stream `k`. -/
def rnd (s k i : Nat) : Nat := ((s * 1000003 + k * 7777777 + i * 99991 + 12345) ^ 7 + 3 * i + s) % (P - 2) + 1
def rndF (s k n : Nat) : List F := (List.range n).map fun i => fe (rnd s k i)
def rndBytes (s k n : Nat) : Bytes := (List.range n).map fun i => UInt8.ofNat (rnd s k i % 256)

def le32 (n : Nat) : Bytes := le 32 n

/-- Private inputs: A's values, B's zeros, summed in the engine (`sharedBlock`). -/
def inputBlock (f0 slot n : Nat) : List Instr := sharedBlock f0 n slot

/-! ## Split ECDH -/

def kA : Nat := 8 * 123456789012345678901234567890123
def kB : Nat := 8 * 98765432109876543210987654321987
def serverU : F := montU (mul 777777777 base)

def splitStore (s : Nat) (k : Nat) (cheat : Bool) : Store :=
  let t := (splitAgreeInputs k serverU).getD []
  mkStore [(5, if cheat then [fe 3, fe 4] else t), (6, rndF s 6 1)]
    [(0, rndBytes s 0 32), (1, (splitShare k).getD [])]

def splitScript (me : Party) : Script (Bytes × FieldH × Bool) :=
  (splitBegin sha256 me 0 1).bind fun key =>
    (splitAgree 100 5 6).bind fun r => .done (key, r.1, r.2)

def splitChecks (E : Env) : List String :=
  let r := runPair E fuel (splitScript .a) (splitScript .b) (splitStore 1 kA false) (splitStore 2 kB false)
    { progs := E.progs } { progs := E.progs } {} []
  let want := mul (kA + kB) (Option.getD (liftU serverU) neutral)
  [s!"flow s11-split"] ++ r.lines ++ ["endflow"] ++
  match r.result with
  | some ((key, q, zero), (key', _, _)) =>
    [check "split key share" (key == toBytes (montU (mul (kA + kB) base)) && key == key'),
     check "split agreement" (!zero && r.ideal.fields q.id == some (montU want))]
  | none => [check "split" false]

def cheatSplit (E : Env) : List String :=
  let r := runPair E fuel (splitScript .a) (splitScript .b) (splitStore 1 kA false) (splitStore 2 kB true)
    { progs := E.progs } { progs := E.progs } {} []
  [s!"flow cheat-split-share"] ++ r.lines ++ ["endflow", check "cheat-split-share aborts" r.result.isNone]

/-! ## Nine X25519 agreements on shared swap bits -/

def jobScalar (j : Nat) : Nat := rnd 9 j 0 % 2 ^ 255
def jobU (j : Nat) : F := montU (mul (rnd 9 j 1 % (2 ^ 252)) base)
def swapOf (k : Nat) : List Bool := (List.range 252).map fun t => TlsMpc.X25519Fast.swapBitSpec k.testBit (t + 2)

/-- A's share of the swap bits: random; B's: the XOR with the real bits. -/
def shareA (j : Nat) : List Bool := (List.range 252).map fun t => (rnd 1 (100 + j) t) % 2 == 1
def shareB (j : Nat) : List Bool := (List.zipWith (· ^^ ·) (swapOf (jobScalar j)) (shareA j))

def agreeStore (s : Nat) : Store :=
  mkStore [(10, if s = 1 then (List.range 9).map jobU else (List.range 9).map fun _ => fe 0),
    (11, ((List.range 9).flatMap fun j => if s = 1 then shareA j else shareB j).map TlsMpc.X25519.bitValue),
    (12, rndF s 12 9)] []

def agreeScript : Script (List (FieldH × Bool)) :=
  TlsMpc.Node.Flows.Contacts.seqs (inputBlock 0 10 9) <|
  (TlsMpc.Node.Flows.Convert.sharedBits 100 (9 * 252) 11).bind fun bits =>
    agree 20000 12 ((List.range 9).map fun j => (((bits.drop (252 * j)).take 252), (⟨18 + j⟩ : FieldH)))

def agreeChecks (E : Env) : List String :=
  let r := runPair E fuel agreeScript agreeScript (agreeStore 1) (agreeStore 2) { progs := E.progs } { progs := E.progs } {} []
  [s!"flow s11-agree"] ++ r.lines ++ ["endflow"] ++
  match r.result with
  | some (qs, _) =>
    [check "nine agreements" (qs.length == 9 && (qs.zipIdx).all fun e =>
      r.ideal.fields e.1.1.id == some (TlsMpc.X25519.spec (jobScalar e.2).testBit (jobU e.2)))]
  | none => [check "nine agreements" false]

/-! ## The offset agreement -/

def recipU : F := montU (mul 31337313373133731337 base)
def recip : Value := (liftU recipU).getD neutral
def scal (s : Nat) : Bytes := rndBytes s 30 32
def kOf (s : Nat) : Nat := scalarOf (scal s) % 2 ^ 252
def tau1 : Nat := rnd 3 3 3 % 2 ^ 252
def tau2 : Nat := 2 ^ 252 - 1 - 4321

def offSlots : OffsetSlots := ⟨21, 22, 23, 24, 25⟩

def offsetStore (s : Nat) : Store :=
  mkStore [(20, [if s = 1 then recipU else fe 0]), (21, rndF s 21 1), (22, offsetCoins (scal s)),
    (23, rndF s 23 prepMasks), (26, rndF s 26 128), (27, rndF s 27 1)]
    [(24, rndBytes s 24 32), (25, offsetShare (scal s))]

def offsetScript (me : Party) : Script ((F × FieldH) × (F × FieldH)) :=
  TlsMpc.Node.Flows.Contacts.seqs (inputBlock 0 20 1) <|
  (offsetPrepare sha256 me 100 offSlots ⟨2⟩).bind fun st =>
  (offsetStep 20000 26 st tau1).bind fun r1 =>
  (offsetStepFast 21000 27 st tau2).bind fun r2 => .done (r1, r2)

def offsetChecks (E : Env) : List String :=
  let r := runPair E fuel (offsetScript .a) (offsetScript .b) (offsetStore 1) (offsetStore 2)
    { progs := E.progs } { progs := E.progs } {} []
  let k0 := kOf 1 + kOf 2
  let key0 := mul k0 base
  [s!"flow s11-offset"] ++ r.lines ++ ["endflow"] ++
  match r.result with
  | some (((e1, q1), (e2, q2)), _) =>
    [check "offset step (sum)" (r.ideal.fields q1.id == some (montU (mul (k0 + tau1) recip))),
     check "offset step (fast)" (r.ideal.fields q2.id == some (montU (mul (k0 + tau2) recip))),
     check "ephemeral keys" (some e1 == ephemeralKey key0 tau1 && some e2 == ephemeralKey key0 tau2),
     check "recode carries" ((recode 0 tau1 64).2 == 0 && (recode 0 tau2 64).2 == 0)]
  | none => [check "offset" false]

/-! ## The hinted programs -/

def hU (j : Nat) : F := if j = 2 then fe 0 else montU (mul (rnd 4 j 4 % 2 ^ 252) base)
def hPoint (j : Nat) : Value := (liftU (hU j)).getD neutral

def liftSlots : LiftSlots := ⟨31, 32, 33, 34⟩

def maskRnd (s n : Nat) : List (Nat × Nat × Bool) :=
  (List.range n).map fun i => (rnd s 35 i, rnd s 36 i % 8, rnd s 37 i % 2 == 1)

def liftStore (s : Nat) (n : Nat) (us : List F) (cheatPoint : Bool) : List (Nat × List F) :=
  let li := liftLocalInputs (maskRnd s n)
  [(30, if s = 1 then us else us.map fun _ => fe 0), (31, li.1),
   (32, if cheatPoint then [fe 5] ++ li.2.drop 1 else li.2), (33, rndF s 33 n), (34, rndF s 34 (5 * n))]

/-- The hint slot 40, the torsion-hint slot 41, from the lifted points (indices 0, 1, 2). -/
def hintedLocal (me : Party) (cheatHint : Bool) (ls : List Lifted) (σ : Store) : Option Store :=
  let live := (ls.zipIdx).filter fun e => !e.1.zero
  match hintsLocal me 32 40 live σ with
  | none => none
  | some σ1 =>
    let σ1 := if cheatHint then σ1.setElems 40 ((σ1.elems 40).set 7 (fe 9)) else σ1
    torsionLocal me 32 41 live σ1

def sigH : Nat := rnd 5 5 5 % 2 ^ 256
def sigS : Nat := rnd 5 6 6 % 2 ^ 253
def bitsPub (k w : Nat) : List F := (List.range w).map fun i => TlsMpc.X25519.bitValue (k.testBit i)

def identity (s : Nat) : Bytes := rndBytes s 50 32
def identityBits : Nat := scalarOf (TlsMpc.Node.Flows.Random.xorBytes (identity 1) (identity 2))

def hintedSecond (ls : List Lifted) : Script (List (FieldH × Bool) × List (FieldH × FieldH) × List (FieldH × FieldH)) :=
  let live := ls.filter fun l => !l.zero
  (tables 100000 ⟨40, 42, 43⟩ live).bind fun ts =>
  (sharedBits 120000 44).bind fun kb =>
  let jobs : List HintedJob := (ls.foldl (fun (st : List HintedJob × Nat) l =>
      if l.zero then (st.1 ++ [⟨kb, none, l.valid⟩], st.2)
      else (st.1 ++ [⟨kb, ts[st.2]?, l.valid⟩], st.2 + 1)) ([], 0)).1
  (agreeHinted 130000 45 46 jobs).bind fun us =>
  TlsMpc.Node.Flows.Contacts.seqs (baseTableBlock 140000 ++ publics 142000 (bitsPub 1 1 ++ bitsPub sigH 256 ++ bitsPub sigS 253)) <|
  (signatures 143000 47 (hs 140000 1024) [(ts.headD [], hs 142000 510)]).bind fun sg =>
  (torsion 150000 41 48 49 live).bind fun tr => .done (us, sg, tr)

def hintedStaged (me : Party) (cheatHint : Bool) :
    Staged (List Lifted) (List (FieldH × Bool) × List (FieldH × FieldH) × List (FieldH × FieldH)) where
  first := TlsMpc.Node.Flows.Contacts.seqs (inputBlock 0 30 3) (lift 100 liftSlots (hs 6 3))
  step := hintedLocal me cheatHint
  second := hintedSecond

def hintedStore (s : Nat) (cheatPoint : Bool) : Store :=
  mkStore (liftStore s 3 ((List.range 3).map hU) cheatPoint ++
    [(42, rndF s 42 (126 * 2)), (43, rndF s 43 (252 * 2)), (44, shareCoins (identity s)), (45, rndF s 45 2),
     (46, rndF s 46 2), (47, rndF s 47 2), (48, rndF s 48 2), (49, rndF s 49 8)]) []

def isNeutralExt (I : Ideal) (h : FieldH × FieldH) : Bool :=
  I.fields h.1.id == some 0 && I.fields h.2.id == some 0

def hintedChecks (E : Env) : List String :=
  let r := runStaged E (hintedStaged .a false) (hintedStaged .b false) (hintedStore 1 false) (hintedStore 2 false)
    { progs := E.progs } {}
  let k := identityBits
  [s!"flow s11-hinted"] ++ r.lines ++ ["endflow"] ++
  match r.result with
  | some ((us, sg, tr), _) =>
    -- the lift's x sign is the program's root choice: accept P or −P
    let sgWant := sub (mul sigS base) (mul sigH (hPoint 0))
    let sgWant' := sub (mul sigS base) (mul sigH (neg (hPoint 0)))
    [check "hinted agreements" (us.length == 3 && (us.zipIdx).all fun e =>
        if e.2 = 2 then e.1.2 else
          r.ideal.fields e.1.1.id == some (TlsMpc.X25519.spec k.testBit (hU e.2))),
     check "signature point" (match sg with
        | [(x, y)] =>
          (r.ideal.fields x.id == some sgWant.1 && r.ideal.fields y.id == some sgWant.2) ||
          (r.ideal.fields x.id == some sgWant'.1 && r.ideal.fields y.id == some sgWant'.2)
        | _ => false),
     check "torsion (prime-order points)" (tr.length == 2 && tr.all (isNeutralExt r.ideal))]
  | none => [check "hinted" false]

def cheatHinted (E : Env) (name : String) (point hint : Bool) : List String :=
  let r := runStaged E (hintedStaged .a false) (hintedStaged .b hint) (hintedStore 1 false) (hintedStore 2 point)
    { progs := E.progs } {}
  [s!"flow {name}"] ++ r.lines ++ ["endflow", check s!"{name} aborts" r.result.isNone]

/-! ## Op 66 with an invalid key in the batch -/

/-- Four recipients; the third has u = 2, not a curve coordinate (its key is refused). -/
def cU (j : Nat) : F := if j = 2 then fe 2 else montU (mul (rnd 6 j 6 % 2 ^ 252) base)

def prepSlots : PrepareSlots :=
  { lift := liftSlots, scalars := 60, linkPool := 61, maskPool := 62, hints := 63, links := 64, masks := 65,
    bits := 66, shares := 67, nonce := 68, rho := 69, qslot := 70 }

def prepStore (s : Nat) : Store :=
  mkStore (liftStore s 4 ((List.range 4).map cU) false ++
    [(61, rndF s 61 (126 * 4)), (62, rndF s 62 (1150 * 4)), (69, rndF s 69 3), (70, rndF s 70 3),
     (71, shareCoins (identity s))])
    [(60, rndBytes s 60 (32 * 4)), (68, rndBytes s 68 32)]

/-- Op 66 after the identity key's shared bits (slot 71; its outputs at 200000 …). `cheat`: party B
replaces its K₀ halves, after committing, by an encoding that is not a point. -/
def prepStaged (me : Party) (cheat : Bool) : Staged (List Lifted × List Bool) (Bytes × List (OffsetState × FieldH)) :=
  let st := prepareContacts sha256 me 1000 prepSlots (hs 8 4) (hs 200000 251)
  { first := TlsMpc.Node.Flows.Contacts.seqs (inputBlock 0 30 4) <|
      (TlsMpc.Node.Flows.Convert.sharedBits 198996 251 71).bind fun _ => st.first,
    step := fun r σ => (st.step r σ).map fun σ' =>
      if cheat then σ'.setBytes 67 ((List.range 3).flatMap fun _ => le32 2) else σ',
    second := st.second }

def prepChecks (E : Env) : List String :=
  let r := runStaged E (prepStaged .a false) (prepStaged .b false) (prepStore 1) (prepStore 2) { progs := E.progs } {}
  let ok := [0, 1, 3]
  [s!"flow s11-prepare"] ++ r.lines ++ ["endflow"] ++
  match r.result with
  | some ((status, sts), _) =>
    [check "prepare status" (status == [255, 255, 0, 255]),
     check "static agreements" (sts.length == 3 && (sts.zip ok).all fun e =>
        r.ideal.fields e.1.2.id == some (TlsMpc.X25519.spec identityBits.testBit (cU e.2))),
     check "initial keys" ((sts.zip ok).all fun e =>
        e.1.1.key == mul (scalarOf ((rndBytes 1 60 (32 * 4)).drop (32 * e.2) |>.take 32) % 2 ^ 252 +
          scalarOf ((rndBytes 2 60 (32 * 4)).drop (32 * e.2) |>.take 32) % 2 ^ 252) base)]
  | none => [check "prepare" false]

def cheatCommit (E : Env) : List String :=
  let r := runStaged E (prepStaged .a false) (prepStaged .b true) (prepStore 1) (prepStore 2) { progs := E.progs } {}
  [s!"flow cheat-k0-half"] ++ r.lines ++ ["endflow", check "cheat-k0-half aborts" r.result.isNone]

def all (table : List (String × Program)) : List String :=
  let E := mkEnv table
  let progLines := table.map fun e => s!"prog {hex (ascii e.1)} {hex (ascii (TlsMpc.FieldDag.V3.render e.2))}"
  let pins := table.map fun e => s!"pin {e.1} {hex (sha256 (ascii (TlsMpc.FieldDag.V3.render e.2)))}"
  let valid := table.map fun e => check s!"valid {e.1}" e.2.valid
  let shapes := table.map fun e => check s!"shape {e.1}"
    (match shapeOf e.1 with
     | some (i, m, o, _) => e.2.inputs == i && e.2.masks == m && e.2.outputs.length == o
     | none => e.1 == "field-bit-check" || e.1 == "field-bit-xor")
  progLines ++ pins ++ valid ++ shapes ++ splitChecks E ++ cheatSplit E ++ agreeChecks E ++ offsetChecks E ++
    hintedChecks E ++ cheatHinted E "cheat-mask-point" true false ++ cheatHinted E "cheat-hint" false true ++
    prepChecks E ++ cheatCommit E

end S11V

def main : IO Unit := do
  let t ← IO.asTask (do
    -- the clock keeps the compiler from hoisting the compilation out of the big-stack thread
    let t0 ← IO.monoNanosNow
    let names := if t0 = 0 then [] else S11V.progNames
    let table := names.filterMap fun n => (S11V.compileOne n).map fun p => (n, p)
    for l in S11V.all table do IO.println l) (prio := .dedicated)
  match t.get with
  | .ok _ => pure ()
  | .error e => IO.println s!"error {e}"
