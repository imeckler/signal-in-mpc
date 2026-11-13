import TlsMpc.Node.Flows.Registry
import TlsMpc.Node.Flows.TlsProofs
import TlsMpc.Sha256

/-!
Test vectors of the S12 flows (GHASH key-power shares, the record seal, the typed record open)
for the stand-in two-party test `node_worker/tests/s12_pair.rs`, computed by the Lean model itself
(`Engine/Model.lean` `idealStep` on each agreed batch) from the Lean scripts, with the parties'
local GHASH arithmetic (`Local/Ghash.lean`) between the scripts as `TlsBackend` does it. Not part
of the library; nothing imports it.

    lake env lean --run node_worker/tests/lean/S12Vectors.lean      # stdout → node_worker/tests/s12_vectors.txt

STAND-IN CIRCUITS. The model's circuits here are the kernels' SPECIFICATIONS on concrete bytes
(the right-hand sides of `gcmKeyShare_spec`, `gcmMultiply_spec`, `gcmTag_spec`, `gcmCheck_spec`,
`tlsSealCtr_spec`, and for `tls-open-typed` the concrete `RecordClass.openParsed` and
`TypedOpen.direct`, equal to the kernel by `openParsed_refines`, `direct_refines`), so the vectors
do not evaluate the symbolic kernels. Every evaluation is listed (`eval` lines) and the Rust
stand-in engines compute circuits by that table: the test checks the shells (agreement, `check`,
marks, plumbing, openings to one party) against Lean's model, not the circuits.

TEST KEYS. The traffic blocks are fresh XORs of the two parties' fixed test shares (as
`TlsKernels::fresh` does with random ones): a `Config.test` deviation.

Format (one item per line):
  sig NAME_HEX IN_WIDTH MARKS           a circuit's signature (marks as digits)
  eval NAME_HEX IN_HEX OUT_HEX          one copy's input and output bits (one byte per bit)
  flow NAME / endflow                   two parties, batch by batch (as s10_vectors.txt)
    round, party a|b, batch HEX, verdict ok|refused I, reply HEX
    finished | abort a|b REASON | error ...
  check NAME ok|FAIL                    a value read from the model, against the Lean reference
-/

open TlsMpc.Node
open TlsMpc.Node.Engine
open TlsMpc.Node.Flows
open TlsMpc.Node.Flows.Contacts (bitsOf bytesOf B8)
open TlsMpc.Node.Flows.TlsBase (bitsOfW wOfBits bitsOfWs wsOfBits)

namespace S12V

abbrev W := BitVec 128

def digit (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'
def hexByte (b : UInt8) : String := String.ofList [digit (b.toNat / 16), digit (b.toNat % 16)]
def hex (bs : Bytes) : String := String.join (bs.map hexByte)
def hexBits (b : Bits) : String := hex (b.map fun x => if x then 1 else 0)

def sha256 (m : Bytes) : Bytes :=
  (TlsMpc.Sha256.hash TlsMpc.Sha256.concrete (m.map fun b => BitVec.ofNat 8 b.toNat)).map
    fun b => UInt8.ofNat b.toNat

def markCode : Mark → String
  | .never => "0"
  | .pub => "1"
  | .toA => "2"
  | .toB => "3"
  | .revealable => "4"

/-! ## The stand-in circuits: the kernels' specifications -/

def specC (inBytes : Nat) (marks : List Mark) (f : B8 → B8) : Circuit :=
  ⟨8 * inBytes, marks, fun v => bitsOf (f (bytesOf v))⟩

def xorAll (a b : B8) : B8 := TlsMpc.Aes.addRoundKey TlsMpc.Gcm.concrete.aes a b

def keyShareSpec (v : B8) : B8 :=
  xorAll (TlsMpc.Aes.encryptExpanded TlsMpc.Gcm.concrete.aes 10 (TlsMpc.HybridKernel.expandedOf (v.take 60))
    (TlsMpc.Gcm.zeros TlsMpc.Gcm.concrete 16)) ((v.drop 60).take 16)

def multiplySpec (v : B8) : B8 :=
  let g := TlsMpc.Gcm.concrete
  let s := fun (i : Nat) => (v.drop (16 * i)).take 16
  xorAll (g.unpack (TlsMpc.Ghash.multiply g.field (g.pack (xorAll (s 0) (s 1))) (g.pack (xorAll (s 2) (s 3))))) (s 4)

def tagSpec (v : B8) : B8 := xorAll (xorAll (v.take 16) ((v.drop 16).take 16)) ((v.drop 32).take 16)

def checkSpec (v : B8) : B8 :=
  let K := v.take 60
  let seqB := (v.drop 60).take 8
  [if xorAll (xorAll (TlsMpc.HybridKernel.padOf K seqB) ((v.drop 68).take 16)) ((v.drop 84).take 16) =
      (v.drop 100).take 16 then 255 else 0]

def sealCtrSpec (kind size padding : Nat) (v : B8) : B8 :=
  let K := v.take 60
  let seqB := (v.drop 60).take 8
  let inner := TlsMpc.TlsRecord.inner TlsMpc.Gcm.concrete ((v.drop 68).take size) kind padding
  TlsMpc.TlsRecord.header TlsMpc.Gcm.concrete (inner.length + 16) ++ TlsMpc.HybridKernel.ctrOf K seqB inner ++
    TlsMpc.HybridKernel.padOf K seqB

def typedSpec (cap : Nat) (v : B8) : B8 :=
  let parser := v.take 11
  let block := (v.drop 11).take 60
  let seqB := (v.drop 71).take 8
  let record := (v.drop 79).take cap
  let size := (v.drop (79 + cap)).take 2
  let accepted := (v.drop (81 + cap)).getD 0 0
  let parsed := TlsMpc.RecordClass.openParsed TlsMpc.Gcm.concrete TlsMpc.ByteAuth.concrete
    (TlsMpc.HybridKernel.expandedOf block) (TlsMpc.TlsRecord.nonce TlsMpc.Gcm.concrete ((block.drop 48).take 12) seqB)
    record (size.getD 0 0) (size.getD 1 0) accepted
  let out := TlsMpc.TypedOpen.direct TlsMpc.Signal.Word64.concrete TlsMpc.ByteAuth.concrete parser parsed
  [TlsMpc.TypedOpen.handshakeBit TlsMpc.ByteAuth.concrete parsed] ++ out.take 2 ++ (out.drop 2).take 11 ++
    (out.drop 13).take 2 ++ out.drop 15 ++ parsed

def cap : Nat := 32
def typedOutBytes : Nat := (typedSpec cap (List.replicate 114 0)).length

def typedMarks : List Mark :=
  List.replicate 24 .pub ++ List.replicate (8 * (typedOutBytes - 3)) .never

def circuitTable : List (String × Circuit) :=
  [("xor-bit", Conv.xorBitC),
   ("gcm-key-share", specC 76 (List.replicate 128 .toB) keyShareSpec),
   ("gcm-multiply", specC 80 (List.replicate 128 .toB) multiplySpec),
   ("gcm-tag", specC 48 (List.replicate 128 .pub) tagSpec),
   ("gcm-check", specC 116 (List.replicate 8 .never) checkSpec),
   ("tls-parser-initial", specC 1 (List.replicate 88 .never) (fun _ => List.replicate 11 0)),
   ("tls-seal-ctr 23 4 0", specC 72 (List.replicate 80 .pub ++ List.replicate 128 .never) (sealCtrSpec 23 4 0)),
   ("tls-open-typed 32", specC (114) typedMarks (typedSpec cap))]

def env : Env :=
  { circuits := fun n => (circuitTable.find? (fun e => ascii e.1 == n)).map (·.2), hash := sha256 }

/-! ## Batches, the functionality with its evaluations listed -/

def emitBatch (c : Ctx) (b : List Wire) : Ctx × List String :=
  let lines := [s!"batch {hex (encodeBatch b)}"]
  match checkBatch env.sigs c (b.map InstrP.skel) with
  | .ok (c', _) => (c', lines ++ ["verdict ok"])
  | .error i => (c, lines ++ [s!"verdict refused {i}"])

/-- The circuit evaluations of one agreed instruction (one line per copy). -/
def evals (w : Wire) (I : Ideal) : List String :=
  match w with
  | .run _ name copies input =>
    match env.circuits name, I.bools input.id with
    | some c, some v =>
      (List.range copies).map fun j =>
        let x := (v.drop (j * c.inWidth)).take c.inWidth
        s!"eval {hex name} {hexBits x} {hexBits (c.eval x)}"
    | _, _ => []
  | _ => []

/-- `runWires` (Model.lean), listing every circuit evaluation. -/
def runWiresLog : List Wire → List Wire → Ideal → Option (Ideal × List Release × List Release × List String)
  | [], [], I => some (I, [], [], [])
  | wA :: as, wB :: bs, I =>
    match idealStep env .a wA wB.part I with
    | some (I', toA, toB) =>
      match runWiresLog as bs I' with
      | some (I'', ra, rb, ev) => some (I'', toA.toList ++ ra, toB.toList ++ rb, evals wA I ++ ev)
      | none => none
    | none => none
  | _, _, _ => none

structure Run where
  σA : Store
  σB : Store
  ca : Ctx
  cb : Ctx
  I : Ideal
  lines : List String
  evals : List String

/-- Two parties, batch by batch, through the model's functionality. -/
def runPair {α : Type} : Nat → Script α → Script α → Run → Run × Option (α × α)
  | 0, _, _, r => ({ r with lines := r.lines ++ ["error fuel"] }, none)
  | fuel + 1, sa, sb, r =>
    let ba := nextBatch sha256 .a r.σA sa
    let bb := nextBatch sha256 .b r.σB sb
    match ba.rest, bb.rest with
    | .aborted x, _ => ({ r with lines := r.lines ++ [s!"abort a {x}"] }, none)
    | _, .aborted x => ({ r with lines := r.lines ++ [s!"abort b {x}"] }, none)
    | ra0, rb0 =>
      if ba.wires.isEmpty && bb.wires.isEmpty then
        match ra0, rb0 with
        | .finished x, .finished y => (r, some (x, y))
        | _, _ => ({ r with lines := r.lines ++ ["error shape"] }, none)
      else
        match runWiresLog ba.wires bb.wires r.I with
        | none => ({ r with lines := r.lines ++ ["error functionality"] }, none)
        | some (I', relA, relB, ev) =>
          let ea := emitBatch r.ca ba.wires
          let eb := emitBatch r.cb bb.wires
          let lines := ["round", "party a"] ++ ea.2 ++ [s!"reply {hex (encodeReplies (relA.map (·.datum)))}"] ++
            ["party b"] ++ eb.2 ++ [s!"reply {hex (encodeReplies (relB.map (·.datum)))}"]
          let r' := { r with ca := ea.1, cb := eb.1, I := I', lines := r.lines ++ lines, evals := r.evals ++ ev }
          match ra0, rb0 with
          | .finished x, .finished y => (r', some (x, y))
          | .waiting ia ka, .waiting ib kb =>
            let rA := absorb sha256 .a ia r.σA (if ia.releasesTo .a then relA.getLast? else none)
            let rB := absorb sha256 .b ib r.σB (if ib.releasesTo .b then relB.getLast? else none)
            runPair fuel (ka rA.1) (kb rB.1) { r' with σA := rA.2, σB := rB.2 }
          | _, _ => ({ r' with lines := r'.lines ++ ["error shape"] }, none)

/-- Run one script on both parties (the same script: its private data are slots). -/
def step {α : Type} (r : Run) (s : Script α) : Run × Option α :=
  let (r', res) := runPair 64 s s r
  (r', res.map (·.1))

/-! ## The scenario -/

def bytesN (seed n : Nat) : B8 := (List.range n).map fun i => BitVec.ofNat 8 (seed * 131 + i * 29 + 7)

/-- 480 bits per party: its share of a fresh traffic block. -/
def interleave480 : List Nat := (List.range 480).flatMap fun i => [i, 480 + i]

def freshScript (n slot : Nat) : Script BoolH :=
  Contacts.seqs [.boolInputBoth ⟨n⟩ ⟨n + 1⟩ 480 true false slot, .concat ⟨n + 2⟩ [⟨n⟩, ⟨n + 1⟩],
    .pick ⟨n + 3⟩ ⟨n + 2⟩ interleave480, .run ⟨n + 4⟩ (ascii "xor-bit") 480 ⟨n + 3⟩] (.done ⟨n + 4⟩)

def shareA (k : Nat) : B8 := bytesN (10 + k) 60
def shareB (k : Nat) : B8 := bytesN (20 + k) 60
def block (k : Nat) : B8 := xorAll (shareA k) (shareB k)

def putBits (σ : Store) (slot : Nat) (b : Bits) : Store := σ.setBits slot b

/-- GHASH shares for a direction to 4 powers: the key share, a local squaring, one engine round. -/
def ghash (r : Run) (n : Nat) (traffic : BoolH) (base : Nat) (maskA roundMaskA : B8) :
    Run × List W × List W :=
  let r := { r with σA := putBits r.σA base (bitsOf maskA) }
  let (r, _) := step r (Ghash.keyShareScript n traffic base (base + 1))
  let a1 : List W := [Local.Ghash.ofBytes maskA]
  let b1 : List W := [wOfBits (r.σB.bits (base + 1))]
  let a2 := Local.Ghash.extend a1 2 []
  let b2 := Local.Ghash.extend b1 2 []
  let c := Local.Ghash.oddCount 2 4
  let r := { r with
    σA := ((putBits r.σA (base + 2) (bitsOfWs (Local.Ghash.lefts a2 4))).setBits (base + 3) (bitsOfW (a2.getD 0 0))).setBits
      (base + 4) (bitsOf roundMaskA),
    σB := (putBits r.σB (base + 2) (bitsOfWs (Local.Ghash.lefts b2 4))).setBits (base + 3) (bitsOfW (b2.getD 0 0)) }
  let (r, _) := step r (Ghash.roundScript (n + 3) c (base + 2) (base + 3) (base + 4) (base + 5))
  let a4 := Local.Ghash.extend a2 4 (wsOfBits c (bitsOf roundMaskA))
  let b4 := Local.Ghash.extend b2 4 (wsOfBits c (r.σB.bits (base + 5)))
  (r, a4, b4)

def sharedOk (a b : List W) (h : W) : Bool :=
  (List.range 4).all fun k => a.getD k 0 ^^^ b.getD k 0 == Local.Ghash.power h k

def seqB : B8 := List.replicate 8 0
def ping : B8 := [112, 105, 110, 103]
def hello : B8 := [104, 101, 108, 108, 111, 33]

def bitsAt (r : Run) (h : BoolH) : Bits := (r.I.bools h.id).getD []

def main : IO Unit := do
  for (name, c) in circuitTable do
    IO.println s!"sig {hex (ascii name)} {c.inWidth} {String.join (c.outMarks.map markCode)}"
  let r0 : Run := { σA := ({} : Store).setBits 1 (bitsOf (shareA 0)) |>.setBits 2 (bitsOf (shareA 1)),
                    σB := ({} : Store).setBits 1 (bitsOf (shareB 0)) |>.setBits 2 (bitsOf (shareB 1)),
                    ca := {}, cb := {}, I := {}, lines := ["flow s12-tls"], evals := [] }
  -- the client and server traffic blocks (fresh XORs)
  let (r, kc) := step r0 (freshScript 0 1)
  let (r, ks) := step r (freshScript 5 2)
  let some kc := kc | IO.println "error client block"
  let some ks := ks | IO.println "error server block"
  -- GHASH shares of the client key: 4 powers (key share, a local square, one round of c = 1)
  let (r, a, b) := ghash r 10 kc 10 (bytesN 3 16) (bytesN 4 16)
  let ghashOk := sharedOk a b (TlsMpc.HybridKernel.hashKeyOf (block 0))
  -- seal "ping" (23, padding 0): ctr, halves, tag
  let (r, content) := step r (Tls.publicScript 30 ping)
  let some content := content | IO.println "error content"
  let (r, sealed) := step r (Tls.sealCtrScript 31 kc content seqB 23 4 0)
  let some (hc, pad) := sealed | IO.println "error seal ctr"
  let hA := Local.Ghash.half a (hc.take 5) (hc.drop 5)
  let hB := Local.Ghash.half b (hc.take 5) (hc.drop 5)
  let r := { r with σA := r.σA.setBits 40 (bitsOfW hA), σB := r.σB.setBits 40 (bitsOfW hB) }
  let (r, tag) := step r (Tls.tagScript 36 pad 40)
  let some tag := tag | IO.println "error tag"
  let reference := TlsMpc.TlsRecord.sealCore TlsMpc.Gcm.concrete (((block 0).drop 32).take 16)
    (((block 0).drop 48).take 12) seqB ping 23 0
  let sealOk := hc ++ tag == reference
  -- open "hello!" sealed by the server under its block, sequence 0
  let (r, a', b') := ghash r 50 ks 20 (bytesN 5 16) (bytesN 6 16)
  let (r, parser) := step r (Tls.parserScript 64)
  let some parser := parser | IO.println "error parser"
  let wire := TlsMpc.TlsRecord.sealCore TlsMpc.Gcm.concrete (((block 1).drop 32).take 16)
    (((block 1).drop 48).take 12) seqB hello 23 0
  let hdr := wire.take 5
  let ct := (wire.drop 5).take (wire.length - 21)
  let r := { r with σA := r.σA.setBits 41 (bitsOfW (Local.Ghash.half a' hdr ct)),
                    σB := r.σB.setBits 41 (bitsOfW (Local.Ghash.half b' hdr ct)) }
  let padded := wire ++ List.replicate (cap - wire.length) 0
  let (r, o) := step r (Tls.openScript 70 parser ks seqB (wire.drop (wire.length - 16)) padded
    ((wire.drop 3).take 2) cap 41)
  let some o := o | IO.println "error open"
  let openOk := o.event == [1, 0] && bytesOf (bitsAt r o.length) == [0, 6] &&
    (bytesOf (bitsAt r o.content)).take 6 == hello
  -- a forged tag: the check refuses, the bit is 0 and the event [0, 0] (fatal), nothing else
  let forged := (wire.drop (wire.length - 16)).map (· ^^^ 1)
  let r := { r with σA := r.σA.setBits 42 (bitsOfW (Local.Ghash.half a' hdr ct)),
                    σB := r.σB.setBits 42 (bitsOfW (Local.Ghash.half b' hdr ct)) }
  let (r, o2) := step r (Tls.openScript 90 o.parser ks (List.replicate 7 0 ++ [1]) forged padded
    ((wire.drop 3).take 2) cap 42)
  let forgedOk := match o2 with
    | some o2 => o2.event == [0, 0]
    | none => false
  for e in r.evals.eraseDups do IO.println e
  for l in r.lines do IO.println l
  IO.println "finished"
  IO.println "endflow"
  IO.println s!"check ghash {if ghashOk then "ok" else "FAIL"}"
  IO.println s!"check seal {if sealOk then "ok" else "FAIL"}"
  IO.println s!"check open {if openOk then "ok" else "FAIL"}"
  IO.println s!"check forged {if forgedOk then "ok" else "FAIL"}"

end S12V

def main : IO Unit := S12V.main
