import TlsMpc.Node.Flows.Registry
import TlsMpc.Sha256

/-!
Test vectors of the S10 flows (masks, conversions, inversion) for the stand-in two-party test
`node_worker/tests/s10_pair.rs`, computed by the Lean model itself (TlsMpc/Node/Engine/Model.lean
`runWires` on each agreed batch) from the Lean scripts. Not part of the library; nothing imports it.

    lake env lean --run node_worker/tests/lean/S10Vectors.lean      # stdout → node_worker/tests/s10_vectors.txt

TEST PARAMETERS. `Masks.testParams 3 1` (N = 3 kept references in buckets of B = 2, one bit block):
a `Config.test` deviation, far below the statistical target, never a deployed profile
(`Masks.testParams_not_deployed`). The deployed profile is `Masks.profile 16 0` (B = 22).

STAND-IN PROGRAMS. `field-bit-check`, `field-bit-xor`, `field-recompose` are written here as V3 rows
with the values `Conv.ProgsLoaded` states (the exported texts come from the re-export; their pins
are placeholders in loader.rs until then). `field-mask-sub` and `field-quotient` are the Lean
programs themselves (`Conv.maskSub`, `FieldDagV3.quotient`).

Format (one item per line):
  sig NAME_HEX IN_WIDTH MARKS           a word circuit's signature (marks as digits)
  prog NAME_HEX TEXT_HEX                a V3 program's text (FieldDagV3.render)
  native NAME TEXT_HEX SHA256           an S10 natively written program and its pin
  flow NAME / endflow                   two parties, batch by batch
    round, party a|b, batch HEX, verdict ok|refused I, reply HEX   (reply: what the model releases)
    finished | abort a|b REASON | error ...
  check NAME ok|FAIL                    P-CUT (a) and the conversions' values, read from the model
-/

open TlsMpc.Node.Engine
open TlsMpc.FieldDag (F modulus)
open TlsMpc.FieldDag.V3 (Program Row)
open TlsMpc.Node.Flows
open TlsMpc.Node.Flows.Conv

namespace S10V

def digit (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'
def hexByte (b : UInt8) : String := String.ofList [digit (b.toNat / 16), digit (b.toNat % 16)]
def hex (bs : Bytes) : String := String.join (bs.map hexByte)

def sha256 (m : Bytes) : Bytes :=
  (TlsMpc.Sha256.hash TlsMpc.Sha256.concrete (m.map fun b => BitVec.ofNat 8 b.toNat)).map
    fun b => UInt8.ofNat b.toNat

def fe (n : Nat) : F := TlsMpc.FieldDag.ofNat n

def markCode : Mark → String
  | .never => "0"
  | .pub => "1"
  | .toA => "2"
  | .toB => "3"
  | .revealable => "4"

/-! ## Stand-in programs -/

def bitCheckP : Program :=
  { inputs := 1, masks := 0, rows := [.input 0, .const 1, .sub 0 1, .mul 0 2], outputs := [(3, .pub)] }

def bitXorP : Program :=
  { inputs := 2, masks := 0, rows := [.input 0, .input 1, .add 0 1, .mul 0 1, .const 2, .mul 4 3, .sub 2 5],
    outputs := [(6, .never)] }

/-- Horner: acc₂₅₄ = in₂₅₄, accᵢ = inᵢ + 2·accᵢ₊₁, then acc₀ − in₂₅₅. -/
def recomposeRows : List Row × Nat :=
  (List.range 254).foldl (fun (st : List Row × Nat) k =>
    let n := st.1.length
    (st.1 ++ [Row.mul 256 st.2, Row.add (253 - k) n], n + 1))
    ((List.range 256).map Row.input ++ [Row.const 2], 254)

def recomposeP : Program :=
  { inputs := 256, masks := 0, rows := recomposeRows.1 ++ [Row.sub recomposeRows.2 255],
    outputs := [(recomposeRows.1.length, .pub)] }

def progTable : List (String × Program) :=
  [("field-bit-check", bitCheckP), ("field-bit-xor", bitXorP), ("field-recompose", recomposeP),
   ("field-mask-sub", maskSub), ("field-quotient", TlsMpc.FieldDag.V3.quotient)]

def circuitTable : List (String × Circuit) :=
  [("modadd", modaddC), ("modadd-open", modaddOpenC), ("finalize-mask", finalizeMaskC),
   ("finalize-bits", finalizeBitsC), ("into-field-open", intoFieldOpenC), ("xor-bit", xorBitC),
   ("xor-bit-open", xorBitOpenC), ("swap-bits", swapBitsC)]

def env : Env :=
  { circuits := fun n => (circuitTable.find? (fun e => ascii e.1 == n)).map (·.2),
    hash := sha256,
    programs := fun n => (progTable.find? (fun e => ascii e.1 == n)).map (·.2) }

def start : Ctx := { progs := env.progs }

/-! ## Batches, verdicts, replies -/

def showShape : Shape → String
  | .unit => "u"
  | .bits n => s!"b{n}"
  | .elems n => s!"e{n}"
  | .bytes n => s!"x{n}"

def emitBatch (c : Ctx) (b : List Wire) : Ctx × List String :=
  let lines := [s!"batch {hex (encodeBatch b)}"]
  match checkBatch env.sigs c (b.map InstrP.skel) with
  | .ok (c', _) => (c', lines ++ ["verdict ok"])
  | .error i => (c, lines ++ [s!"verdict refused {i}"])

/-- Two parties, batch by batch, through the model's functionality (`runWires`). -/
def runPair {α : Type} : Nat → Script α → Script α → Store → Store → Ctx → Ctx → Ideal → List String →
    List String × Option (α × α) × Ideal
  | 0, _, _, _, _, _, _, I, acc => (acc ++ ["error fuel"], none, I)
  | fuel + 1, sa, sb, σA, σB, ca, cb, I, acc =>
    let ba := nextBatch sha256 .a σA sa
    let bb := nextBatch sha256 .b σB sb
    match ba.rest, bb.rest with
    | .aborted r, _ => (acc ++ [s!"abort a {r}"], none, I)
    | _, .aborted r => (acc ++ [s!"abort b {r}"], none, I)
    | ra0, rb0 =>
      if ba.wires.isEmpty && bb.wires.isEmpty then
        match ra0, rb0 with
        | .finished x, .finished y => (acc ++ ["finished"], some (x, y), I)
        | _, _ => (acc ++ ["error shape"], none, I)
      else
        match runWires env ba.wires bb.wires I with
        | none => (acc ++ ["error functionality"], none, I)
        | some (I', relA, relB) =>
          let ea := emitBatch ca ba.wires
          let eb := emitBatch cb bb.wires
          let lines := ["round", "party a"] ++ ea.2 ++ [s!"reply {hex (encodeReplies (relA.map (·.datum)))}"] ++
            ["party b"] ++ eb.2 ++ [s!"reply {hex (encodeReplies (relB.map (·.datum)))}"]
          match ra0, rb0 with
          | .finished x, .finished y => (acc ++ lines ++ ["finished"], some (x, y), I')
          | .waiting ia ka, .waiting ib kb =>
            let rA := absorb sha256 .a ia σA (if ia.releasesTo .a then relA.getLast? else none)
            let rB := absorb sha256 .b ib σB (if ib.releasesTo .b then relB.getLast? else none)
            runPair fuel (ka rA.1) (kb rB.1) rA.2 rB.2 ea.1 eb.1 I' (acc ++ lines)
          | _, _ => (acc ++ lines ++ ["error shape"], none, I')

/-! ## Stores -/

def P : Nat := Conv.P

/-- Candidate j of party `s` (1: A, 2: B): a canonical value at least 32. -/
def cand (s j : Nat) : Nat := ((s * 1000003 + j * 7777777 + 12345) ^ 5 + 32 * s) % (P - 64) + 32

def p : Masks.Params := Masks.testParams 3 1

def slots : Masks.Slots :=
  { bits := 10, elems := 11, coins := 100, cutNonce := 0, cutValue := 1, bucketNonce := 2, bucketValue := 3 }

def bytes32 (s k : Nat) : Bytes := (List.range 32).map fun i => UInt8.ofNat (s * 37 + k * 101 + i * 7 + 1)

/-- The word of A's private input u (W2F), and its 8 bits x (B2F). -/
def uVal : Nat := 2 ^ 254 + 987654321
def xBits : Bits := [true, false, false, true, true, false, true, false]
/-- The local bits each party contributes to `sharedBits` (6 of them). -/
def localBits (s : Nat) : Bits := (List.range 6).map fun i => (s + i) % 3 == 0

/-- Party `s`'s store, honest. `cands` overrides its candidates (bits and elements apart). -/
def store (s : Nat) (cbits : Nat → Bits) (celem : Nat → F) (coins : Nat → List F) : Store :=
  { bits := fun j => if j = 10 then (List.range p.M).flatMap cbits
      else if j = 20 then word uVal else if j = 21 then xBits else [],
    elems := fun j => if j = 11 then (List.range p.M).map celem
      else if 100 ≤ j ∧ j < 100 + p.M then coins (j - 100)
      else if j = 30 then (localBits s).map TlsMpc.X25519.bitValue
      else if j = 40 then [fe (1000 + s)] else [],
    bytes := fun k => if k < 4 then bytes32 s k else [] }

def honestStore (s : Nat) : Store :=
  store s (fun j => word (cand s j)) (fun j => fe (cand s j)) (fun j => (word (cand s j)).map TlsMpc.X25519.bitValue)

/-! ## The scripts -/

def generate (me : Party) : Script MaskPool := Masks.generate p 0 0 sha256 me slots

/-- Generation, then each conversion and the inversion on the pool. Handles from fixed offsets
above the generation's blocks. -/
def demo (me : Party) : Script (List Nat) := do
  let pool ← generate me
  Script.instr (.boolInput ⟨400⟩ .a 255 false false 20)
  match pool.takeWord with
  | none => .abort "no mask"
  | some (m1, pool) =>
    let fh ← Convert.wordToField 410 3000 ⟨400⟩ m1
    match pool.takeWord with
    | none => .abort "no mask"
    | some (m2, pool) =>
      let wh ← Convert.fieldToWord 420 3010 fh m2
      Script.instr (.boolInput ⟨430⟩ .a 8 false false 21)
      match pool.takeBits 8 with
      | none => .abort "no pairs"
      | some (ps, _) =>
        let bs ← Convert.bitsToField 440 3020 ⟨430⟩ ps
        let sb ← Convert.sharedBits 3100 6 30
        let (q, zero) ← Inversion.quotientScript 3200 40 fh fh
        pure ([fh.id, wh.id] ++ bs.map (·.id) ++ sb.map (·.id) ++ [q.id, if zero then 1 else 0])

def fuel : Nat := 400

def flowLines {α : Type} (name : String) (sa sb : Script α) (σA σB : Store) : List String × Option (α × α) × Ideal :=
  let r := runPair fuel sa sb σA σB start start {} []
  ([s!"flow {name}"] ++ r.1 ++ ["endflow"], r.2.1, r.2.2)

/-! ## Checks of the honest values (P-CUT (a), conversions) -/

def check (name : String) (ok : Bool) : String := s!"check {name} {if ok then "ok" else "FAIL"}"

def maskChecks (pool : MaskPool) (I : Ideal) : List String :=
  pool.words.map (fun m =>
    match I.bools m.bits.id, I.fields m.field.id with
    | some w, some f => check s!"mask {m.bits.id}" (w.length == 255 && natOf w == f.val)
    | _, _ => check s!"mask {m.bits.id}" false) ++
  [check "pairs" (pool.bits.all fun q =>
    match I.bools q.bit.id, I.fields q.field.id with
    | some [b], some f => f == TlsMpc.X25519.bitValue b
    | _, _ => false)]

def demoChecks (hs : List Nat) (I : Ideal) : List String :=
  match hs with
  | fh :: wh :: rest =>
    let bs := rest.take 8
    let sb := (rest.drop 8).take 6
    let q := (rest.drop 14).getD 0 0
    [check "w2f" (I.fields fh == some (fe uVal)),
     check "f2w" (I.bools wh == some (word (uVal % P))),
     check "b2f" ((bs.zip xBits).all fun e => I.fields e.1 == some (TlsMpc.X25519.bitValue e.2)),
     check "shared-bits" ((sb.zip ((localBits 1).zip (localBits 2))).all fun e =>
        I.fields e.1 == some (TlsMpc.X25519.bitValue (e.2.1 ^^ e.2.2))),
     check "quotient" (I.fields q == some (fe uVal * TlsMpc.FieldDag.V3.inverseFast (fe uVal)))]
  | _ => [check "demo" false]

/-! ## The cheating cases (party B deviates; `Config.test` `deviate=NAME`) -/

def seed : Bytes := Random.xorBytes (bytes32 1 1) (bytes32 2 1)
def seed2 : Bytes := Random.xorBytes (bytes32 1 3) (bytes32 2 3)
def π₁ : List Nat := (Random.permOf sha256 (Masks.domain p "cut") seed p.M).getD []
def π₂ : List Nat := (Random.permOf sha256 (Masks.domain p "bucket") seed2 p.K).getD []
def member (j k : Nat) : Nat := Masks.member p π₁ π₂ j k
def cutCand : Nat := π₁.getD 0 0

def flip0 (w : Bits) : Bits := match w with | b :: r => (!b) :: r | [] => []

/-- A wrong cut candidate: B's Boolean bits of one cut candidate inconsistent with its element. -/
def cheatCut : Store :=
  store 2 (fun j => if j = cutCand then flip0 (word (cand 2 j)) else word (cand 2 j)) (fun j => fe (cand 2 j))
    (fun j => (word (cand 2 j)).map TlsMpc.X25519.bitValue)

/-- A wrong bucket member (kept out of the cut): its bits off by one from its element. -/
def cheatBucket : Store :=
  store 2 (fun j => if j = member 0 1 then flip0 (word (cand 2 j)) else word (cand 2 j)) (fun j => fe (cand 2 j))
    (fun j => (word (cand 2 j)).map TlsMpc.X25519.bitValue)

/-- A non-bit: B's coins of its bit-block reference with a 0, 1 pair replaced by 2, 0 (the
recomposition still matches; the bit check does not). -/
def nonbit (cs : List F) : List F :=
  match (List.range (cs.length - 1)).find? (fun i => cs.getD i 0 == fe 0 && cs.getD (i + 1) 0 == fe 1) with
  | some i => (cs.set i (fe 2)).set (i + 1) (fe 0)
  | none => cs

def cheatNonbit : Store :=
  store 2 (fun j => word (cand 2 j)) (fun j => fe (cand 2 j))
    (fun j => if j = member 0 0 then nonbit ((word (cand 2 j)).map TlsMpc.X25519.bitValue)
      else (word (cand 2 j)).map TlsMpc.X25519.bitValue)

/-- A reference ≥ p: B's word-mask reference p + 5 (bits) with the element 5 (consistent mod p),
its bucket member small and consistent, so the cut and the buckets pass and the flag fails. -/
def cheatReference : Store :=
  store 2 (fun j => if j = member 1 0 then word (P + 5) else if j = member 1 1 then word 7 else word (cand 2 j))
    (fun j => if j = member 1 0 then fe 5 else if j = member 1 1 then fe 7 else fe (cand 2 j))
    (fun j => (word (cand 2 j)).map TlsMpc.X25519.bitValue)

/-- A wrong bit block: B's first coin of its reference flipped (the recomposition fails). -/
def cheatBitblock : Store :=
  store 2 (fun j => word (cand 2 j)) (fun j => fe (cand 2 j))
    (fun j => let cs := (word (cand 2 j)).map TlsMpc.X25519.bitValue
      if j = member 0 0 then (cs.set 0 (fe 1 - cs.getD 0 0)) else cs)

def allLines : List String :=
  let sigLines := circuitTable.map fun e =>
    s!"sig {hex (ascii e.1)} {e.2.inWidth} {String.join (e.2.outMarks.map markCode)}"
  let progLines := progTable.map fun e => s!"prog {hex (ascii e.1)} {hex (ascii (TlsMpc.FieldDag.V3.render e.2))}"
  let native := [s!"native field-mask-sub {hex (ascii (TlsMpc.FieldDag.V3.render maskSub))} " ++
    s!"{hex (sha256 (ascii (TlsMpc.FieldDag.V3.render maskSub)))}"]
  let valid := progTable.map fun e => check s!"valid {e.1}" e.2.valid
  let gen := flowLines "s10-generate" (generate .a) (generate .b) (honestStore 1) (honestStore 2)
  let genChecks := match gen.2.1 with
    | some (pool, _) => maskChecks pool gen.2.2
    | none => [check "generate" false]
  let demoR := flowLines "s10-demo" (demo .a) (demo .b) (honestStore 1) (honestStore 2)
  let demoC := match demoR.2.1 with
    | some (hs, _) => demoChecks hs demoR.2.2
    | none => [check "demo" false]
  let cheats := [("cheat-cut", cheatCut), ("cheat-bucket", cheatBucket), ("cheat-nonbit", cheatNonbit),
    ("cheat-reference", cheatReference), ("cheat-bitblock", cheatBitblock)]
  let cheatLines := cheats.map fun c =>
    let r := flowLines c.1 (generate .a) (generate .b) (honestStore 1) c.2
    r.1 ++ [check s!"{c.1} aborts" r.2.1.isNone]
  sigLines ++ progLines ++ native ++ valid ++ gen.1 ++ genChecks ++ demoR.1 ++ demoC ++ cheatLines.flatten

end S10V

def main : IO Unit := do
  for l in S10V.allLines do
    IO.println l
