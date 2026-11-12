import TlsMpc.Node.Flows.Upgrade
import TlsMpc.Sha256

/-!
Test vectors for the Rust interpreter (node_worker/src/interp.rs, handles.rs), computed by the
Lean specification (TlsMpc/Node/Engine.lean) itself. Not part of the library; nothing imports it.

Regenerate (one Lean job, from the repository root):
    python3 .deps/lowering-scratch/s9r_vectors.py
which runs `lake env lean --run node_worker/tests/lean/EngineVectors.lean` and writes its output
to node_worker/tests/engine_vectors.txt. node_worker/tests/engine_vectors.rs reads that file.

Format (one item per line, `key value`):
  sig NAME_HEX IN_WIDTH MARKS          a circuit signature used by `check` (marks as digits)
  sha256-abc HEX                       SHA-256("abc") as computed here (sanity of the hash below)
  case NAME / end                      batches checked in sequence from the empty context
    batch HEX                          encodeBatch
    skeleton HEX                       skeletonBytes
    verdict ok SHAPES | refused INDEX  checkBatch over the skeletons (SHAPES: u, bN, eN, xN; -)
    ctx TEXT                           the context after the batch (unchanged when refused)
  flow NAME / endflow                  two honest parties, rounds of one batch each
    round
    party a|b, then batch/skeleton/verdict/ctx as above for that party, then
    reply HEX                          encodeReplies of what this party is released (honest run)
    result a|b TEXT                    the script's result (hex), when it is a script
  decode HEX none|some HEX             decodeBatch, and the re-encoding when it succeeds
  replies HEX                          encodeReplies of a fixed datum list
Marks: 0 never, 1 pub, 2 toA, 3 toB, 4 revealable.
-/

open TlsMpc.Node.Engine
open TlsMpc.FieldDag (F modulus)

namespace S9R

def digit (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'
def hexByte (b : UInt8) : String := String.ofList [digit (b.toNat / 16), digit (b.toNat % 16)]
def hex (bs : Bytes) : String := String.join (bs.map hexByte)

def sha256 (m : Bytes) : Bytes :=
  (TlsMpc.Sha256.hash TlsMpc.Sha256.concrete (m.map fun b => BitVec.ofNat 8 b.toNat)).map
    fun b => UInt8.ofNat b.toNat

def fe (n : Nat) : F := TlsMpc.FieldDag.ofNat n

def powMod (b e m : Nat) : Nat := Id.run do
  let mut r := 1
  let mut x := b % m
  let mut k := e
  while k > 0 do
    if k % 2 == 1 then r := r * x % m
    x := x * x % m
    k := k / 2
  return r

def inv (x : F) : F := fe (powMod x.val (modulus - 2) modulus)

def bs (s : String) : Bits := s.toList.map (· == '1')

def byteBits (b : UInt8) : Bits := (List.range 8).map fun i => (b.toNat >>> i) % 2 == 1
def bytesBits (l : Bytes) : Bits := (l.map byteBits).flatten

def markCode : Mark → String
  | .never => "0"
  | .pub => "1"
  | .toA => "2"
  | .toB => "3"
  | .revealable => "4"

def marksStr (ms : List Mark) : String := String.join (ms.map markCode)

def sigTable : List (String × Sig) :=
  [("tls-reveal 7", ⟨128, List.replicate 24 .pub⟩),
   ("toy", ⟨4, [.never, .toA, .toB, .pub]⟩),
   ("noin", ⟨0, [.pub, .toB]⟩)]

def sigs (n : Bytes) : Option Sig := (sigTable.find? (fun e => ascii e.1 == n)).map (·.2)

def natsStr (l : List Nat) : String := ",".intercalate (l.map toString)

def showCtx (c : Ctx) : String :=
  let bools := c.bools.mergeSort (fun x y => decide (x.1 ≤ y.1))
  let fields := c.fields.mergeSort (fun x y => decide (x.1 ≤ y.1))
  "B[" ++ ";".intercalate (bools.map fun e => s!"{e.1}:{marksStr e.2.marks}:{if e.2.once then 1 else 0}") ++
  "]F[" ++ ";".intercalate (fields.map fun e => s!"{e.1}:{markCode e.2}") ++
  "]SB[" ++ natsStr (c.seenB.mergeSort (fun a b => decide (a ≤ b))) ++
  "]SF[" ++ natsStr (c.seenF.mergeSort (fun a b => decide (a ≤ b))) ++ "]"

def showShape : Shape → String
  | .unit => "u"
  | .bits n => s!"b{n}"
  | .elems n => s!"e{n}"
  | .bytes n => s!"x{n}"

/-- `check` over a whole batch, as the shell runs it: the first refused index, or the context
after the batch and every instruction's shape. -/
def checkBatch (c : Ctx) : List Skel → Nat → Except Nat (Ctx × List Shape)
  | [], _ => .ok (c, [])
  | s :: ss, i =>
    match check sigs c s with
    | none => .error i
    | some (c', sh) =>
      match checkBatch c' ss (i + 1) with
      | .error j => .error j
      | .ok (c'', shs) => .ok (c'', sh :: shs)

def emitBatch (c : Ctx) (b : List Wire) : Ctx × List String :=
  let lines := [s!"batch {hex (encodeBatch b)}", s!"skeleton {hex (skeletonBytes b)}"]
  match checkBatch c (b.map InstrP.skel) 0 with
  | .ok (c', shs) =>
    let sh := if shs.isEmpty then "-" else ",".intercalate (shs.map showShape)
    (c', lines ++ [s!"verdict ok {sh}", s!"ctx {showCtx c'}"])
  | .error i => (c, lines ++ [s!"verdict refused {i}", s!"ctx {showCtx c}"])

def emitBatches (c : Ctx) : List (List Wire) → List String
  | [] => []
  | b :: rest =>
    let r := emitBatch c b
    r.2 ++ emitBatches r.1 rest

def runCase (name : String) (batches : List (List Wire)) : List String :=
  [s!"case {name}"] ++ emitBatches {} batches ++ ["end"]

/-! ## Every instruction once (party A's and party B's wires of the same skeletons) -/

def toy : Bytes := ascii "toy"

def allBatches (me : Party) : List (List Wire) :=
  let mine (v : Bits) : Bits := if me = .a then v else []
  [[.boolInput ⟨1⟩ .a 4 false true (mine (bs "1011")),
    .boolInputBoth ⟨2⟩ ⟨3⟩ 4 true false (if me = .a then bs "0010" else bs "1110"),
    .boolPublic ⟨4⟩ (bs "10"),
    .concat ⟨5⟩ [⟨1⟩, ⟨2⟩],
    .slice ⟨6⟩ ⟨5⟩ 0 4,
    .pick ⟨7⟩ ⟨3⟩ [0, 0, 3],
    .run ⟨8⟩ toy 1 ⟨1⟩,
    .slice ⟨10⟩ ⟨8⟩ 1 2,
    .openBoolTo ⟨10⟩ .a ⟨7⟩ ()],
   [.freeBool ⟨4⟩,
    .openBool ⟨6⟩ ⟨3⟩],
   [.fieldInput [⟨1⟩, ⟨2⟩] [⟨3⟩, ⟨4⟩] .elements true (if me = .a then [fe 11, fe 22] else [fe 33, fe 44]),
    .fieldPublic ⟨5⟩ (fe (2 ^ 200 + 7)),
    .fieldAdd ⟨6⟩ ⟨1⟩ ⟨3⟩,
    .fieldSub ⟨7⟩ ⟨6⟩ ⟨5⟩,
    .fieldScale ⟨8⟩ ⟨7⟩ 12345,
    .fieldDivide ⟨9⟩ ⟨8⟩ (fe 3),
    .fieldMul [⟨10⟩, ⟨11⟩] [(⟨1⟩, ⟨2⟩), (⟨3⟩, ⟨5⟩)],
    .fieldCheck,
    .openField [⟨9⟩, ⟨10⟩] ⟨4⟩],
   [.fieldInput [⟨12⟩] [⟨13⟩] .coins false (if me = .a then [fe 5] else [fe 6]),
    .freeField ⟨11⟩,
    .exchange 5 ⟨9⟩ (if me = .a then [1, 2, 3, 4, 5] else [6, 7, 8, 9, 10])]]

/-! ## Ill-formed batches: every refusal of `check`, and the boundaries next to them -/

def inp (i : Nat) : Wire := .boolInput ⟨i⟩ .a 4 false true (bs "1011")
def inpOnce (i : Nat) : Wire := .boolInput ⟨i⟩ .a 4 true true (bs "1011")
def inpNever (i : Nat) : Wire := .boolInput ⟨i⟩ .b 4 false false []
def fin (a b : Nat) : Wire := .fieldInput [⟨a⟩] [⟨b⟩] .elements true [fe 1]
def coinsNever (a b : Nat) : Wire := .fieldInput [⟨a⟩] [⟨b⟩] .coins false [fe 3]

def cases : List (String × List (List Wire)) :=
  [("reuse-bool", [[inp 1], [inp 1]]),
   ("reuse-after-free", [[inp 1, .freeBool ⟨1⟩], [inp 1]]),
   ("both-same-id", [[.boolInputBoth ⟨1⟩ ⟨1⟩ 2 false false (bs "01")]]),
   ("both-reuse-b", [[inp 2, .boolInputBoth ⟨1⟩ ⟨2⟩ 2 false false (bs "01")]]),
   ("public-reuse", [[inp 1, .boolPublic ⟨1⟩ (bs "1")]]),
   ("public-empty-ok", [[.boolPublic ⟨1⟩ [], .openBool ⟨1⟩ ⟨3⟩]]),
   ("run-unknown", [[inp 1, .run ⟨2⟩ (ascii "nope") 1 ⟨1⟩]]),
   ("run-zero-copies", [[inp 1, .run ⟨2⟩ toy 0 ⟨1⟩]]),
   ("run-dead-input", [[.run ⟨2⟩ toy 1 ⟨1⟩]]),
   ("run-width", [[inp 1, .run ⟨2⟩ toy 2 ⟨1⟩]]),
   ("run-two-copies-ok", [[inp 1, inp 2, .concat ⟨3⟩ [⟨1⟩, ⟨2⟩], .run ⟨4⟩ toy 2 ⟨3⟩]]),
   ("run-out-reuse", [[inp 1, .run ⟨1⟩ toy 1 ⟨1⟩]]),
   ("run-noin-ok", [[.concat ⟨1⟩ [], .run ⟨2⟩ (ascii "noin") 3 ⟨1⟩]]),
   ("run-once-consumed", [[inpOnce 1, .run ⟨2⟩ toy 1 ⟨1⟩, .run ⟨3⟩ toy 1 ⟨1⟩]]),
   ("concat-dead", [[inp 1, .concat ⟨2⟩ [⟨1⟩, ⟨9⟩]]]),
   ("concat-once-twice", [[inpOnce 1, .concat ⟨2⟩ [⟨1⟩, ⟨1⟩]]]),
   ("concat-twice-ok", [[inp 1, .concat ⟨2⟩ [⟨1⟩, ⟨1⟩]]]),
   ("concat-out-is-part", [[inp 1, .concat ⟨1⟩ [⟨1⟩]]]),
   ("slice-lo-gt-hi", [[inp 1, .slice ⟨2⟩ ⟨1⟩ 3 2]]),
   ("slice-hi-out", [[inp 1, .slice ⟨2⟩ ⟨1⟩ 0 5]]),
   ("slice-empty-ok", [[inp 1, .slice ⟨2⟩ ⟨1⟩ 4 4]]),
   ("slice-dead", [[.slice ⟨2⟩ ⟨1⟩ 0 0]]),
   ("pick-out-of-range", [[inp 1, .pick ⟨2⟩ ⟨1⟩ [1, 4]]]),
   ("pick-empty-ok", [[inp 1, .pick ⟨2⟩ ⟨1⟩ []]]),
   ("pick-dead", [[.pick ⟨2⟩ ⟨1⟩ []]]),
   ("open-label0", [[inp 1, .openBool ⟨1⟩ ⟨0⟩]]),
   ("open-never", [[inpNever 1, .openBool ⟨1⟩ ⟨3⟩]]),
   ("open-toA", [[inp 1, .run ⟨2⟩ toy 1 ⟨1⟩, .openBool ⟨2⟩ ⟨3⟩]]),
   ("open-pub-slice-ok", [[inp 1, .run ⟨2⟩ toy 1 ⟨1⟩, .slice ⟨3⟩ ⟨2⟩ 3 4, .openBool ⟨3⟩ ⟨3⟩]]),
   ("open-dead", [[.openBool ⟨1⟩ ⟨3⟩]]),
   ("open-once-twice", [[inpOnce 1, .openBool ⟨1⟩ ⟨3⟩], [.openBool ⟨1⟩ ⟨3⟩]]),
   ("open-mixed-pick", [[inpNever 1, inp 2, .concat ⟨3⟩ [⟨1⟩, ⟨2⟩], .pick ⟨4⟩ ⟨3⟩ [4, 5, 7], .pick ⟨5⟩ ⟨3⟩ [7, 3],
      .openBool ⟨4⟩ ⟨3⟩, .openBool ⟨5⟩ ⟨3⟩]]),
   ("opento-label0", [[inp 1, .run ⟨2⟩ toy 1 ⟨1⟩, .slice ⟨3⟩ ⟨2⟩ 1 2, .openBoolTo ⟨3⟩ .a ⟨0⟩ ()]]),
   ("opento-wrong-recipient", [[inp 1, .run ⟨2⟩ toy 1 ⟨1⟩, .slice ⟨3⟩ ⟨2⟩ 1 2, .openBoolTo ⟨3⟩ .b ⟨5⟩ ()]]),
   ("opento-b-ok", [[inp 1, .run ⟨2⟩ toy 1 ⟨1⟩, .slice ⟨3⟩ ⟨2⟩ 2 3, .openBoolTo ⟨3⟩ .b ⟨5⟩ ()]]),
   ("opento-pub", [[inp 1, .run ⟨2⟩ toy 1 ⟨1⟩, .slice ⟨3⟩ ⟨2⟩ 3 4, .openBoolTo ⟨3⟩ .a ⟨5⟩ ()]]),
   ("opento-revealable", [[inp 1, .openBoolTo ⟨1⟩ .a ⟨5⟩ ()]]),
   ("opento-empty-ok", [[inp 1, .slice ⟨2⟩ ⟨1⟩ 0 0, .openBoolTo ⟨2⟩ .b ⟨5⟩ ()]]),
   ("opento-dead", [[.openBoolTo ⟨2⟩ .b ⟨5⟩ ()]]),
   ("free-dead", [[.freeBool ⟨1⟩]]),
   ("free-twice", [[inp 1, .freeBool ⟨1⟩, .freeBool ⟨1⟩]]),
   ("free-consumed-once", [[inpOnce 1, .concat ⟨2⟩ [⟨1⟩], .freeBool ⟨1⟩]]),
   ("free-once-ok", [[inpOnce 1, .freeBool ⟨1⟩]]),
   ("fieldinput-length", [[.fieldInput [⟨1⟩] [] .elements true [fe 1]]]),
   ("fieldinput-dup", [[.fieldInput [⟨1⟩] [⟨1⟩] .elements true [fe 1]]]),
   ("fieldinput-reuse", [[fin 1 2], [fin 1 3]]),
   ("fieldinput-empty-ok", [[.fieldInput [] [] .coins false []]]),
   ("fieldpublic-reuse", [[fin 1 2, .fieldPublic ⟨2⟩ (fe 0)]]),
   ("fieldadd-dead", [[fin 1 2, .fieldAdd ⟨3⟩ ⟨1⟩ ⟨9⟩]]),
   ("fieldadd-out-reuse", [[fin 1 2, .fieldAdd ⟨1⟩ ⟨1⟩ ⟨2⟩]]),
   ("fieldsub-dead", [[fin 1 2, .fieldSub ⟨3⟩ ⟨9⟩ ⟨1⟩]]),
   ("fieldscale-dead", [[.fieldScale ⟨3⟩ ⟨1⟩ 2]]),
   ("fieldscale-max-ok", [[fin 1 2, .fieldScale ⟨3⟩ ⟨1⟩ (2 ^ 64 - 1)]]),
   ("fielddivide-zero", [[fin 1 2, .fieldDivide ⟨3⟩ ⟨1⟩ (fe 0)]]),
   ("fielddivide-dead", [[.fieldDivide ⟨3⟩ ⟨1⟩ (fe 2)]]),
   ("fieldmul-length", [[fin 1 2, .fieldMul [⟨3⟩] []]]),
   ("fieldmul-dead", [[fin 1 2, .fieldMul [⟨3⟩] [(⟨1⟩, ⟨9⟩)]]]),
   ("fieldmul-dup-out", [[fin 1 2, .fieldMul [⟨3⟩, ⟨3⟩] [(⟨1⟩, ⟨2⟩), (⟨1⟩, ⟨2⟩)]]]),
   ("fieldmul-out-is-operand", [[fin 1 2, .fieldMul [⟨1⟩] [(⟨1⟩, ⟨2⟩)]]]),
   ("fieldmul-empty-ok", [[.fieldMul [] []]]),
   ("openfield-label0", [[fin 1 2, .openField [⟨1⟩] ⟨0⟩]]),
   ("openfield-never", [[coinsNever 1 2, .openField [⟨1⟩] ⟨4⟩]]),
   ("openfield-join-never", [[coinsNever 1 2, .fieldPublic ⟨3⟩ (fe 1), .fieldAdd ⟨4⟩ ⟨1⟩ ⟨3⟩, .openField [⟨4⟩] ⟨4⟩]]),
   ("openfield-join-rev-ok", [[fin 1 2, .fieldPublic ⟨3⟩ (fe 1), .fieldMul [⟨4⟩] [(⟨3⟩, ⟨1⟩)], .openField [⟨4⟩, ⟨3⟩] ⟨4⟩]]),
   ("openfield-pub-ok", [[.fieldPublic ⟨1⟩ (fe 9), .fieldScale ⟨2⟩ ⟨1⟩ 3, .fieldDivide ⟨3⟩ ⟨2⟩ (fe 3), .openField [⟨1⟩, ⟨2⟩, ⟨3⟩] ⟨4⟩]]),
   ("openfield-dead", [[.openField [⟨1⟩] ⟨4⟩]]),
   ("openfield-empty-ok", [[.openField [] ⟨4⟩]]),
   ("openfield-freed", [[fin 1 2, .freeField ⟨1⟩, .openField [⟨1⟩] ⟨4⟩]]),
   ("openfield-twice-ok", [[fin 1 2, .openField [⟨1⟩, ⟨1⟩] ⟨4⟩], [.openField [⟨1⟩] ⟨4⟩]]),
   ("freefield-dead", [[.freeField ⟨1⟩]]),
   ("freefield-reuse-id", [[fin 1 2, .freeField ⟨1⟩, .fieldPublic ⟨1⟩ (fe 0)]]),
   ("exchange-label0", [[.exchange 1 ⟨0⟩ [7]]]),
   ("exchange-len0", [[.exchange 0 ⟨9⟩ []]]),
   ("exchange-max-ok", [[.exchange 65536 ⟨9⟩ []]]),
   ("exchange-too-long", [[.exchange 65537 ⟨9⟩ []]]),
   ("refused-mid-batch", [[inp 1], [inp 2, inp 3, .freeBool ⟨9⟩, inp 4]]),
   ("separate-namespaces-ok", [[inp 1, fin 1 2, .freeBool ⟨1⟩, .freeField ⟨1⟩]]),
   ("once-across-batches", [[inpOnce 1], [.slice ⟨2⟩ ⟨1⟩ 0 2], [.slice ⟨3⟩ ⟨1⟩ 0 2]]),
   ("pick-inherits-once", [[inpOnce 1, .pick ⟨2⟩ ⟨1⟩ [3, 3, 0]], [.openBool ⟨2⟩ ⟨3⟩], [.openBool ⟨2⟩ ⟨3⟩]]),
   ("both-once-concat", [[.boolInputBoth ⟨1⟩ ⟨2⟩ 3 true true (bs "011"), .concat ⟨3⟩ [⟨2⟩, ⟨1⟩], .openBool ⟨3⟩ ⟨3⟩, .openBool ⟨3⟩ ⟨3⟩]]),
   ("large-ids-ok", [[.boolPublic ⟨2 ^ 64 - 1⟩ (bs "1"), .openBool ⟨2 ^ 64 - 1⟩ ⟨2 ^ 64 - 1⟩,
      .fieldPublic ⟨2 ^ 64 - 1⟩ (fe (modulus - 1)), .openField [⟨2 ^ 64 - 1⟩] ⟨2 ^ 64 - 1⟩,
      .exchange 1 ⟨2 ^ 64 - 1⟩ [255]]]),
   ("empty-batch-ok", [[]])]

/-! ## Two-party runs: the flows, and the engine round trips of the end-to-end test -/

def storeOf (seed : Nat) : Store :=
  { bytes := fun j => (List.range 32).map fun i => UInt8.ofNat (seed * 37 + j * 101 + i * 7 + 1) }

def σA : Store := storeOf 1
def σB : Store := storeOf 2

def payloadOf : Wire → Bytes
  | .exchange _ _ p => p
  | _ => []

/-- Two honest parties run their scripts batch by batch; every batch here ends in an exchange
(the flows of this file), whose reply is the other party's payload. -/
partial def runPair {α : Type} (showR : α → String) (sa sb : Script α) (ca cb : Ctx) : List String :=
  let ba := nextBatch sha256 .a σA sa
  let bb := nextBatch sha256 .b σB sb
  match ba.rest, bb.rest with
  | .finished x, .finished y => [s!"result a {showR x}", s!"result b {showR y}"]
  | .waiting _ ka, .waiting _ kb =>
    let pa := (ba.wires.getLast?.map payloadOf).getD []
    let pb := (bb.wires.getLast?.map payloadOf).getD []
    let ea := emitBatch ca ba.wires
    let eb := emitBatch cb bb.wires
    ["round", "party a"] ++ ea.2 ++ [s!"reply {hex (encodeReplies [.bytes pb])}"] ++
      ["party b"] ++ eb.2 ++ [s!"reply {hex (encodeReplies [.bytes pa])}"] ++
      runPair showR (ka (.exchanged pa pb)) (kb (.exchanged pb pa)) ea.1 eb.1
  | .aborted r, _ => [s!"error a {r}"]
  | _, .aborted r => [s!"error b {r}"]
  | _, _ => ["error shape"]

def flowLines {α : Type} (name : String) (showR : α → String) (mk : Party → Script α) : List String :=
  [s!"flow {name}"] ++ runPair showR (mk .a) (mk .b) {} {} ++ ["endflow"]

/-- Fixed two-party rounds: each party's batch and the datums released to it. -/
def fixedFlow (name : String) (rounds : List ((Party → List Wire) × List Datum × List Datum)) : List String :=
  let rec go (ca cb : Ctx) : List ((Party → List Wire) × List Datum × List Datum) → List String
    | [] => []
    | (mk, da, db) :: rest =>
      let ea := emitBatch ca (mk .a)
      let eb := emitBatch cb (mk .b)
      ["round", "party a"] ++ ea.2 ++ [s!"reply {hex (encodeReplies da)}"] ++
        ["party b"] ++ eb.2 ++ [s!"reply {hex (encodeReplies db)}"] ++ go ea.1 eb.1 rest
  [s!"flow {name}"] ++ go {} {} rounds ++ ["endflow"]

/-- Boolean round trip: A inputs the length and content of `tls-reveal 7`, B the one-hot select
mask; the circuit opens the length and the selected byte (HybridKernels.tlsReveal). Then both
parties' bits, plumbing and a public constant, opened. -/
def lengthBytes : Bytes := [5, 0]
def contentBytes : Bytes := [10, 20, 30, 40, 50, 60, 70]
def selectBytes : Bytes := [0, 0, 0, 255, 0, 0, 0]
def revealOut : Bits :=
  bytesBits lengthBytes ++ byteBits ((contentBytes.zip selectBytes).foldl (fun acc p => acc ^^^ (p.1 &&& p.2)) 0)

def bothA : Bits := bs "10110010"
def bothB : Bits := bs "01110100"
def plumbed : Bits :=
  let v := bothA ++ bothB
  ([15, 0, 7, 8].map fun j => v.getD j false) ++ ((v.drop 4).take 8) ++ bs "1100"

def boolRounds : List ((Party → List Wire) × List Datum × List Datum) :=
  [(fun me =>
      [.boolInput ⟨1⟩ .a 72 false false (if me = .a then bytesBits (lengthBytes ++ contentBytes) else []),
       .boolInput ⟨2⟩ .b 56 true false (if me = .b then bytesBits selectBytes else []),
       .concat ⟨3⟩ [⟨1⟩, ⟨2⟩],
       .run ⟨4⟩ (ascii "tls-reveal 7") 1 ⟨3⟩,
       .openBool ⟨4⟩ ⟨3⟩],
    [.bits revealOut], [.bits revealOut]),
   (fun me =>
      [.freeBool ⟨1⟩,
       .boolInputBoth ⟨20⟩ ⟨21⟩ 8 false true (if me = .a then bothA else bothB),
       .concat ⟨22⟩ [⟨20⟩, ⟨21⟩],
       .pick ⟨23⟩ ⟨22⟩ [15, 0, 7, 8],
       .slice ⟨24⟩ ⟨22⟩ 4 12,
       .boolPublic ⟨25⟩ (bs "1100"),
       .concat ⟨26⟩ [⟨23⟩, ⟨24⟩, ⟨25⟩],
       .openBool ⟨26⟩ ⟨3⟩],
    [.bits plumbed], [.bits plumbed])]

def x1 : F := fe (2 ^ 254 + 12345)
def x2 : F := fe 77
def y1 : F := fe (2 ^ 250 + 999)
def y2 : F := fe 31337
def big : F := fe (2 ^ 200 + 7)

def f5 : F := x1 * y1
def f6 : F := f5 + x2
def f9 : F := f6 - big
def f10 : F := f9 * fe 3
def f11 : F := f10 * inv (fe 7)
def f14 : F := fe 1000 + fe 2000
def f15 : F := y2 * fe 5

def fieldRounds : List ((Party → List Wire) × List Datum × List Datum) :=
  [(fun me =>
      [.fieldInput [⟨1⟩, ⟨2⟩] [⟨3⟩, ⟨4⟩] .elements true (if me = .a then [x1, x2] else [y1, y2]),
       .fieldMul [⟨5⟩] [(⟨1⟩, ⟨3⟩)],
       .fieldAdd ⟨6⟩ ⟨5⟩ ⟨2⟩,
       .fieldCheck,
       .openField [⟨5⟩, ⟨6⟩] ⟨4⟩],
    [.elems [f5, f6]], [.elems [f5, f6]]),
   (fun me =>
      [.fieldPublic ⟨7⟩ big,
       .fieldPublic ⟨8⟩ (fe 5),
       .fieldSub ⟨9⟩ ⟨6⟩ ⟨7⟩,
       .fieldScale ⟨10⟩ ⟨9⟩ 3,
       .fieldDivide ⟨11⟩ ⟨10⟩ (fe 7),
       .fieldInput [⟨12⟩] [⟨13⟩] .coins true (if me = .a then [fe 1000] else [fe 2000]),
       .fieldAdd ⟨14⟩ ⟨12⟩ ⟨13⟩,
       .fieldMul [⟨15⟩] [(⟨4⟩, ⟨8⟩)],
       .freeField ⟨1⟩,
       .openField [⟨8⟩, ⟨11⟩, ⟨14⟩, ⟨15⟩] ⟨5⟩],
    [.elems [fe 5, f11, f14, f15]], [.elems [fe 5, f11, f14, f15]])]

/-! ## Decoder vectors -/

def decodeLine (s : Bytes) : String :=
  match decodeBatch s with
  | some b => s!"decode {hex s} some {hex (encodeBatch b)}"
  | none => s!"decode {hex s} none"

def withLast (b : Bytes) (n : Nat) (tail : Bytes) : Bytes := b.take (b.length - n) ++ tail

def decodeVectors : List Bytes :=
  let pub0 := encodeBatch [.fieldPublic ⟨1⟩ (fe 0)]
  let bit1 := encodeBatch [.boolPublic ⟨1⟩ (bs "1")]
  let inp1 := encodeBatch [.boolInput ⟨1⟩ .a 1 false false (bs "1")]
  let exch := encodeBatch [.exchange 3 ⟨1⟩ [1, 2]]
  [encodeBatch [],
   [],
   [0, 0, 0, 0, 0, 0, 0],
   encodeBatch [.fieldCheck] ++ [0],
   (encodeBatch (allBatches .a).head!).dropLast,
   encodeBatch (allBatches .a).head!,
   withLast pub0 32 (le 32 modulus),
   withLast pub0 32 (le 32 (modulus - 1)),
   withLast pub0 32 (le 32 (2 ^ 256 - 1)),
   withLast pub0 32 (le 32 (2 ^ 255)),
   withLast bit1 1 [2],
   withLast bit1 1 [1],
   Enc.u64 1 ++ [0],
   Enc.u64 1 ++ [22],
   Enc.u64 1 ++ [255],
   Enc.u64 (2 ^ 64 - 1) ++ [18],
   Enc.u64 2 ++ [18],
   Enc.u64 2 ++ [18, 18],
   -- boolInput: party byte 2, flag bytes 2
   (inp1.take 17) ++ [2] ++ inp1.drop 18,
   (inp1.take 26) ++ [2] ++ inp1.drop 27,
   (inp1.take 27) ++ [3] ++ inp1.drop 28,
   -- fieldInput kind byte 2
   (encodeBatch [.fieldInput [] [] .coins false []]).take 25 ++ [2, 0] ++ Enc.u64 0,
   -- openBoolTo recipient 2
   withLast (encodeBatch [.openBoolTo ⟨1⟩ .b ⟨1⟩ ()]) 9 ([2] ++ Enc.u64 1),
   -- an exchange whose payload is shorter than its length decodes (the shell checks it later)
   exch,
   -- a list count larger than the input
   Enc.u64 1 ++ [5] ++ Enc.u64 1 ++ Enc.u64 (2 ^ 63) ++ Enc.u64 1,
   -- a field element cut short
   pub0.dropLast]

def replyVectors : List (List Datum) :=
  [[], [.bits (bs "101"), .elems [fe 5, fe (modulus - 1)], .bytes [1, 2, 3]], [.bits [], .elems [], .bytes []]]

def allLines : List String :=
  sigTable.map (fun e => s!"sig {hex (ascii e.1)} {e.2.inWidth} {marksStr e.2.outMarks}") ++
  [s!"sha256-abc {hex (sha256 (ascii "abc"))}"] ++
  runCase "all-a" (allBatches .a) ++
  runCase "all-b" (allBatches .b) ++
  runCase "all-a-one-batch" [(allBatches .a).flatten] ++
  (cases.map fun c => runCase c.1 c.2).flatten ++
  flowLines "random-joint" hex (fun me => TlsMpc.Node.Flows.Random.joint sha256 me 0 1) ++
  flowLines "upgrade-public" hex (fun me => TlsMpc.Node.Flows.Upgrade.publicUpgrade sha256 me 0 1) ++
  fixedFlow "bool" boolRounds ++
  fixedFlow "field" fieldRounds ++
  decodeVectors.map decodeLine ++
  replyVectors.map (fun r => s!"replies {hex (encodeReplies r)}")

end S9R

def main : IO Unit := do
  for l in S9R.allLines do
    IO.println l
