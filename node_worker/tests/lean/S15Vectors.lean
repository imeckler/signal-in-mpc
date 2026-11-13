import TlsMpc.Node.Flows.Registry
import TlsMpc.Node.Flows.RefreshFlowProofs
import TlsMpc.Sha256

/-!
Test vectors of the S15 flows (a two-device refresh: the prekey fetch's seal, the body collected
in two takes, the shape, the nine-step establishment of each device, the scratch's seal and
commit, then a take and a drop) for the stand-in two-party test `node_worker/tests/s15_pair.rs`,
computed by the Lean model (`Engine/Model.lean` `idealStep` on each agreed batch) from the Lean
operations (`Refresh.opFetch`, `opTake`, `opShape`, `opEstablish`, `opScratchSeal`, `opCommit`,
`opDrop`), each operation's `commit` giving the next table and refresh state. Not part of the
library; nothing imports it.

    python3 scratch driver: lake env lean --run node_worker/tests/lean/S15Vectors.lean  → node_worker/tests/s15_vectors.txt

STAND-IN CIRCUITS (labelled; NOT the kernels). The refresh kernels cannot be evaluated at a test
size (Kyber-1024 and the bundle parser have no small parameters; the symbolic kernels are tens of
millions of gates). Every circuit here is a deterministic stand-in with the REAL signature (input
width, output marks: the widths the scripts slice at), a mixing function of its input, with the
opened bytes fixed where the flow reads them (`bundle-fetch-ctr`'s accepted byte 255,
`bundle-rebind`'s `changed` 0, `establish-session`'s status 255; `bundle-shape` flags JSON
punctuation). S11's curve parameter is a stand-in `CurveOps` over three stand-in circuits
(`curve-lift`, `curve-check`, `curve-agree`), releasing nothing. Every evaluation is listed
(`eval` lines); the Rust stand-in engines compute circuits by that table. The test checks the
shells (agreement, `check` with the signatures and marks, plumbing, inputs of both parties,
openings) and the operations' sequencing against Lean's model, not the circuits (the real-engine
fixture, tests/e2e_s15.py, runs the pinned kernels).

Format: as tests/s12_vectors.txt.
-/

open TlsMpc.Node
open TlsMpc.Node.Engine
open TlsMpc.Node.Flows
open TlsMpc.Node.Flows.Contacts (bitsOf bytesOf B8)
open TlsMpc.Signal.BundleResponse (Widths)

namespace S15V

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

/-! ## Stand-in circuits (real signatures) -/

/-- A mixing value of the input bits. -/
def mixOf (seed : Nat) (v : Bits) : Nat := v.foldl (fun acc b => (acc * 3 + (if b then 1 else 0)) % 1000003) seed

/-- `n` stand-in bits from a mixing value. -/
def standBits (s n : Nat) : Bits := (List.range n).map fun j => (s + 7 * j + j / 3) % 5 < 2

/-- A stand-in circuit: `inW` input bits, the given output marks; the output is `pre` (fixed opened
bits) followed by mixing bits. -/
def standC (inW : Nat) (marks : List Mark) (seed : Nat) (pre : Bits := []) : Circuit :=
  ⟨inW, marks, fun v => pre ++ standBits (mixOf seed v) (marks.length - pre.length)⟩

def nev (n : Nat) : List Mark := List.replicate n .never
def pub (n : Nat) : List Mark := List.replicate n .pub

/-- `bundle-shape`: one flag per byte, 255 for JSON punctuation (the real kernel's meaning). -/
def punct (b : BitVec 8) : Bool := b.toNat ∈ [123, 125, 91, 93, 58, 44, 34]
def shapeC (cap : Nat) : Circuit :=
  ⟨8 * cap, pub (8 * cap), fun v => bitsOf ((bytesOf v).map fun b => if punct b then 255 else 0)⟩

def frame : B8 := (List.range 40).map fun i => BitVec.ofNat 8 (i * 11 + 3)
def mask : B8 := [1, 2, 3, 4]
def cert : Nat := 24

def w0 : Widths := ⟨1, 1, 1, 0, 1⟩
def w1 : Widths := ⟨1, 2, 1, 1, 1⟩
def start0 : Nat := TlsMpc.Signal.BundleResponse.firstItem
def start1 : Nat := start0 + Refresh.itemSize w0 + 1
def total : Nat := start1 + Refresh.itemSize w1 + 2
def cap : Nat := Refresh.shapeCapacity total

/-- The slot kernel's input bytes for an item (head, before, item slots, after, end, widths). -/
def slotIn (first last oneTime : Bool) : Nat :=
  73 + (if first then 0 else 1) + TlsMpc.Signal.BundleResponse.size
    (TlsMpc.Signal.BundleResponse.item (TlsMpc.Signal.BundleSlots.slots oneTime)) + (if last then 0 else 1) + 2 + 5

def slotOut (oneTime : Bool) : Nat := (Refresh.slotOutWidths oneTime).sum

def sessionIn (oneTime : Bool) : Nat :=
  8 + 8 + 255 * 3 + (if oneTime then 255 else 0) + 255 + 8 * 32 + 8 * 1568 + 255 * 3 + 8 * (32 + 32 + cert + 16 + 16 + 8 + 1 + 4 + 4) +
    (if oneTime then 32 else 0) + 8 * 8

def circuitTable : List (String × Circuit) :=
  [("bundle-fetch-ctr 40 6 10 50", standC (8 * (60 + 8 + 319 + 40 + 4)) (pub (8 * (1 + 5 + 41)) ++ nev 128) 1 (bitsOf [255])),
   ("bundle-shape " ++ toString cap, shapeC cap),
   ("bundle-slot 1 0 0", standC (8 * slotIn true false false) (nev (8 * slotOut false)) 2),
   ("bundle-slot 0 1 1", standC (8 * slotIn false true true) (nev (8 * slotOut true)) 3),
   ("establish-points 0", standC (8 * 64) (nev 510) 4),
   ("establish-points 1", standC (8 * 96) (nev 765) 5),
   ("establish-challenges", standC (255 * 2 + 8 * (32 + 64 + 1568 + 64)) (nev 1020) 6),
   ("establish-verified", standC (255 * 5 + 8 * 128) (nev 8) 7),
   ("bundle-rebind", standC (8 * (319 + 1 + 1 + 32)) (nev 264 ++ pub 8) 8 []),
   ("kem-hash kyber", standC (8 * 1632) (nev (8 * 97)) 9),
   ("kem-ntt", standC (8 * 32) (nev (8 * 1536)) 10),
   ("kem-matrix 0", standC (8 * 1568) (nev (8 * 1537)) 11),
   ("kem-matrix 1", standC (8 * 1568) (nev (8 * 1537)) 12),
   ("kem-matrix 2", standC (8 * 1568) (nev (8 * 1537)) 13),
   ("kem-matrix 3", standC (8 * 1568) (nev (8 * 1537)) 14),
   ("kem-u 0", standC (8 * 3104) (nev (8 * 352)) 15),
   ("kem-u 1", standC (8 * 3104) (nev (8 * 352)) 16),
   ("kem-u 2", standC (8 * 3104) (nev (8 * 352)) 17),
   ("kem-u 3", standC (8 * 3104) (nev (8 * 352)) 18),
   ("kem-v", standC (8 * 3168) (nev (8 * 160)) 19),
   ("kem-finish kyber", standC (8 * 1605) (nev (8 * 1601)) 20),
   ("establish-session 24 0", standC (sessionIn false) (pub 8 ++ nev (8 * (cert + 319 + 1616 + 192))) 21 (bitsOf [255])),
   ("establish-session 24 1", standC (sessionIn true) (pub 8 ++ nev (8 * (cert + 319 + 1616 + 192))) 22 (bitsOf [255])),
   ("contact-seal " ++ toString (2 * Refresh.deviceContent),
     standC (8 * (68 + 2 * Refresh.deviceContent)) (pub (8 * (2 * Refresh.deviceContent + 16))) 23),
   ("curve-lift", standC 255 (nev 765) 24),
   ("curve-check", standC (255 * 2 + 510 * 2) (nev 1020) 25),
   ("curve-agree 2", standC 510 (nev (255 * 6)) 26),
   ("curve-agree 3", standC 765 (nev (255 * 7)) 27)]

/-- Rebind's opened `changed` is the last byte: zero (the identity key is the stored one). -/
def fixRebind (c : Circuit) : Circuit := ⟨c.inWidth, c.outMarks, fun v => (c.eval v).take 264 ++ List.replicate 8 false⟩

def lookupC (n : Bytes) : Option Circuit :=
  (circuitTable.find? (fun e => ascii e.1 == n)).map fun e => if e.1 = "bundle-rebind" then fixRebind e.2 else e.2

def env : Env := { circuits := lookupC, hash := sha256 }

/-! ## The stand-in curve parameter (S11's place) -/

def curve : Refresh.CurveOps where
  liftIds := (4, 0)
  checkIds := (6, 0)
  agreeIds := (10, 0)
  lift c p := Contacts.seqs [.run ⟨c.bool⟩ (ascii "curve-lift") 1 p,
      .slice ⟨c.bool + 1⟩ ⟨c.bool⟩ 0 255, .slice ⟨c.bool + 2⟩ ⟨c.bool⟩ 255 510, .slice ⟨c.bool + 3⟩ ⟨c.bool⟩ 510 765,
      .freeBool ⟨c.bool⟩] (.done (⟨c.bool + 1⟩, ⟨c.bool + 2⟩, ⟨c.bool + 3⟩))
  check c x y e p := Contacts.seqs [.concat ⟨c.bool⟩ [x, y, e, p], .run ⟨c.bool + 1⟩ (ascii "curve-check") 1 ⟨c.bool⟩,
      .slice ⟨c.bool + 2⟩ ⟨c.bool + 1⟩ 0 255, .slice ⟨c.bool + 3⟩ ⟨c.bool + 1⟩ 255 510,
      .slice ⟨c.bool + 4⟩ ⟨c.bool + 1⟩ 510 765, .slice ⟨c.bool + 5⟩ ⟨c.bool + 1⟩ 765 1020,
      .freeBool ⟨c.bool⟩, .freeBool ⟨c.bool + 1⟩] (.done (⟨c.bool + 2⟩, ⟨c.bool + 3⟩, ⟨c.bool + 4⟩, ⟨c.bool + 5⟩))
  agree c a b o :=
    let k := if o.isSome then 7 else 6
    Contacts.seqs ([.concat ⟨c.bool⟩ ([a, b] ++ o.toList),
        .run ⟨c.bool + 1⟩ (ascii ("curve-agree " ++ toString (k - 4))) 1 ⟨c.bool⟩] ++
        (List.range k).map (fun j => (.slice ⟨c.bool + 2 + j⟩ ⟨c.bool + 1⟩ (255 * j) (255 * (j + 1)) : Instr)) ++
        [.freeBool ⟨c.bool⟩, .freeBool ⟨c.bool + 1⟩])
      (.done ((List.range k).map fun j => ⟨c.bool + 2 + j⟩))
  kinds := []

def acct (certH sender : BoolH) : Refresh.Account := ⟨certH, cert, sender⟩

/-! ## Batches, the functionality with its evaluations listed (as S12Vectors) -/

def emitBatch (c : Ctx) (b : List Wire) : Ctx × List String :=
  let lines := [s!"batch {hex (encodeBatch b)}"]
  match checkBatch env.sigs c (b.map InstrP.skel) with
  | .ok (c', _) => (c', lines ++ ["verdict ok"])
  | .error i => (c, lines ++ [s!"verdict refused {i}"])

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

def step {α : Type} (r : Run) (s : Script α) : Run × Option α :=
  let (r', res) := runPair 64 s s r
  (r', res.map (·.1))

/-! ## The scenario -/

def bytesN (seed n : Nat) : B8 := (List.range n).map fun i => BitVec.ofNat 8 (seed * 131 + i * 29 + 7)

/-- A body with the two items where `layout?` would place them (JSON punctuation where the
template has it is irrelevant to the stand-ins; the shape opens what the bytes are). -/
def body : B8 :=
  (bytesN 1 start0 ++ bytesN 2 (Refresh.itemSize w0) ++ [44] ++ bytesN 3 (Refresh.itemSize w1) ++ [93, 125])

def setupScript : Script (BoolH × BoolH × BoolH × BoolH × BoolH × BoolH) :=
  Contacts.seqs [.boolPublic ⟨0⟩ (bitsOf (bytesN 4 60)), .boolPublic ⟨1⟩ (bitsOf (bytesN 5 319)),
      .boolPublic ⟨2⟩ (bitsOf (bytesN 6 60)), .boolPublic ⟨3⟩ (bitsOf body),
      .boolPublic ⟨4⟩ (bitsOf (bytesN 7 cert)), .boolPublic ⟨5⟩ (List.replicate 255 true)]
    (.done (⟨0⟩, ⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩, ⟨5⟩))

def contact : Nat := 7

def main : IO Unit := do
  for (name, c) in circuitTable do
    IO.println s!"sig {hex (ascii name)} {c.inWidth} {String.join (c.outMarks.map markCode)}"
  let σA : Store := ({} : Store).setBits 3 (bitsOf (bytesN 8 32))
  let σB : Store := ({} : Store).setBits 3 (bitsOf (bytesN 9 32))
  let r0 : Run := { σA, σB, ca := {}, cb := {}, I := {}, lines := ["flow s15-refresh"], evals := [] }
  let (r, hs) := step r0 setupScript
  let some (key, state, traffic, received, certH, sender) := hs | IO.println "error setup"
  let e : Contacts.Entry := { key := some key, state := some state, size := 319, kinds := [0] }
  let t0 : Contacts.Table := { entries := [(contact, e)], ctr := { bool := 10 } }
  let st0 : Refresh.RState := {}
  -- the fetch's seal, first phase (op 56)
  let r := { r with lines := r.lines ++ ["stage fetch"] }
  let f := Refresh.opFetch t0 st0 contact traffic (List.replicate 8 0) frame mask 6 10 50
  let (r, fr) := step r f.script
  let some fr := fr | IO.println "error fetch"
  let (t, st) := f.commit fr
  let fetchOk := fr.1.length == 5 + 41
  let (r, _) := step r (Tls.dropScript [fr.2])
  -- the body in two takes (op 57)
  let half := total / 2
  let o1 := Refresh.opTake t st received 0 half
  let (r, h1) := step r o1.script
  let some h1 := h1 | IO.println "error take 1"
  let (t, st) := o1.commit h1
  let o2 := Refresh.opTake t st received half (total - half)
  let (r, h2) := step r o2.script
  let some h2 := h2 | IO.println "error take 2"
  let (t, st) := o2.commit h2
  -- the shape (op 59)
  let o3 := Refresh.opShape t st (fun _ => true)
  let (r, flags) := step r o3.script
  let some (some flags) := flags | IO.println "error shape"
  let (t, st) := o3.commit (some flags)
  let shapeOk := flags.length == total && flags == body.map punct
  -- two devices, nine steps each (op 60)
  let r := { r with lines := r.lines ++ ["stage establish"] }
  let mut rm := r
  let mut tm := t
  let mut stm := st
  let mut statuses : List Nat := []
  for (index, start, w) in [(0, start0, w0), (1, start1, w1)] do
    for s in List.range 9 do
      let op := Refresh.opEstablish curve (acct certH sender) tm stm contact 1234 index 2 s start w 3
      let (r', res) := step rm op.script
      rm := r'
      match res with
      | some res =>
        let (t', st') := op.commit res
        tm := t'
        stm := st'
        if s == 8 then statuses := statuses ++ [res.1]
      | none => IO.println s!"error establish {index} {s}"
  let r := rm
  let t := tm
  let st := stm
  let readyOk := st.ready && statuses == [255, 255] && st.done.length == 2
  -- the scratch's seal (op 64) and commit (op 65)
  let o4 := Refresh.opScratchSeal t st contact cert (List.replicate 7 0 ++ [1])
  let (r, sealed) := step r o4.script
  let some sealed := sealed | IO.println "error scratch seal"
  let entriesBefore := t.entries.map (·.1)
  let stateBefore := (t.find? contact).bind (·.state)
  let (t, st) := o4.commit sealed
  let sealOk := sealed.2.length == 2 * Refresh.deviceContent + 16 && (t.find? contact).bind (·.state) == stateBefore
  let o5 := Refresh.opCommit t st contact
  let (r, done) := step r o5.script
  let some done := done | IO.println "error commit"
  let (t, st) := o5.commit done
  let commitOk : Bool := match t.find? contact with
    | some e' => e'.state == some sealed.1 && e'.kinds == [1, 2] && e'.size == 2 * Refresh.deviceContent &&
        t.entries.map (·.1) == entriesBefore && st.handles.isEmpty
    | none => false
  -- a take, then a drop: the table is unchanged
  let o6 := Refresh.opTake t st received 0 10
  let (r, h6) := step r o6.script
  let some h6 := h6 | IO.println "error take 3"
  let (t6, st6) := o6.commit h6
  let o7 := Refresh.opDrop t6 st6
  let (r, d) := step r o7.script
  let some d := d | IO.println "error drop"
  let (t7, st7) := o7.commit d
  let dropOk := (t7.find? contact).bind (·.state) == some sealed.1 && st7.handles.isEmpty && (r.I.bools h6.id).isNone
  for ev in r.evals.eraseDups do IO.println ev
  for l in r.lines do IO.println l
  IO.println "finished"
  IO.println "endflow"
  IO.println s!"check fetch {if fetchOk then "ok" else "FAIL"}"
  IO.println s!"check shape {if shapeOk then "ok" else "FAIL"}"
  IO.println s!"check ready {if readyOk then "ok" else "FAIL"}"
  IO.println s!"check sealed {if sealOk then "ok" else "FAIL"}"
  IO.println s!"check commit {if commitOk then "ok" else "FAIL"}"
  IO.println s!"check drop {if dropOk then "ok" else "FAIL"}"

end S15V

def main : IO Unit := S15V.main
