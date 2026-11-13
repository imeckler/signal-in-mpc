import TlsMpc.Node.Flows.Receive
import TlsMpc.Sha256

/-!
Test vectors of the S14 flows (receive a first message: `Receive.takeScript`, `openFirst`,
`session`, then a refused first message) for the stand-in two-party test
`node_worker/tests/s14_pair.rs`, computed by the Lean model itself (`Engine/Model.lean` `idealStep`
on each agreed batch) from the Lean scripts. Not part of the library; nothing imports it.

    lake env lean --run node_worker/tests/lean/S14Vectors.lean      # stdout → node_worker/tests/s14_vectors.txt

STAND-IN TABLES, NOT THE KERNELS. The receive kernels cannot be modelled at a test size (their
layouts are Signal's), and an accepted message needs a genuine sealed-sender envelope, PQXDH and
an XEdDSA signature (tested against libsignal by check_receive_kernels.py, not here). So every
receive kernel is a STAND-IN circuit with the kernel's input width and output marks (the same
closed forms as `loader.rs` `receive_kernel_expected`) whose outputs are FIXED values chosen to
drive the script down the accepted path (statuses 255, well-formed shapes) or, for the second
envelope, to refuse at the certificate length (an invalid second half of sealed sender opens
`00 00`, as `unsealMessage_rejects` says the kernel does). The three V3 receive programs are
stand-in programs of the right input/output counts (one `D` row in `xeddsa-check`). S11's
agreements are a stand-in: party A inputs each agreement word privately. The mask pool is a
stand-in too (party A inputs consistent word masks and bit pairs; not cut-and-choose). What the test
checks is the SHELLS (the agreement, `check` with the kernels' marks, plumbing, openings, program
masks, frees) handing the Lean scripts exactly the replies of Lean's model, and the scripts'
sequencing, gating and freeing; the `check` lines read the model's values against the stand-in
tables.

Format as s12_vectors.txt (sig, eval, prog, flow/round/party/batch/verdict/reply, check).
-/

open TlsMpc.Node
open TlsMpc.Node.Engine
open TlsMpc.Node.Flows
open TlsMpc.Node.Flows.Receive
open TlsMpc.Node.Flows.Contacts (bitsOf bytesOf B8)
open TlsMpc.FieldDag (F)
open TlsMpc.FieldDag.V3 (Program Row)

namespace S14V

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

def fe (n : Nat) : F := TlsMpc.FieldDag.ofNat n
def b8 (l : List Nat) : B8 := l.map fun n => BitVec.ofNat 8 n
def pattern (seed n : Nat) : B8 := (List.range n).map fun i => BitVec.ofNat 8 (seed * 31 + i * 7 + 3)
def zeros (n : Nat) : B8 := List.replicate n 0

/-! ## The public parameters, found by search (they must pass every `ReceiveKernel` check) -/

def certShapeFor (cert : Nat) : Option TlsMpc.Signal.ReceiveFirst.CertShape :=
  certShapeOf cert (b8 [255, 0, 0, 0])

def cert : Nat := ((List.range 500).find? fun c => 67 ≤ c && (certShapeFor c).isSome).getD 0
def cshape : TlsMpc.Signal.ReceiveFirst.CertShape := (certShapeFor cert).getD ⟨0, false, 1, false⟩

def widthsW : List Nat := [0, 2, 1, 1]
def signalVs : List Nat := [1, 1, 48, 0, 0]

def msgN : Nat := ((List.range 800).map (· + 1720)).find? (fun n =>
  match TlsMpc.ReceiveKernel.preKeyShape? n widthsW with
  | some p => (TlsMpc.ReceiveKernel.signalShape? (p.signalSize n) signalVs).isSome
  | none => false) |>.getD 0

def pshape : TlsMpc.Signal.ReceiveFirst.PreKeyShape := (TlsMpc.ReceiveKernel.preKeyShape? msgN widthsW).getD ⟨0, 0, 0, 0⟩

def contentU : Nat := 5 + cert + 1 + TlsMpc.Signal.ReceiveFirst.varintWidth msgN + msgN

def envSize : Nat := ((List.range 200).map (· + contentU)).find? (fun s =>
  TlsMpc.ReceiveKernel.envelopeOk s && TlsMpc.ReceiveKernel.contentBytes s == contentU) |>.getD 0

def c0 : Nat := cert % 128 + 128
def c1 : Nat := cert / 128
def ct : Nat := 48
def cap : Nat := ct - 6
def ownCert : Nat := 260

def paramsOk : Bool :=
  cert != 0 && msgN != 0 && envSize != 0 && TlsMpc.ReceiveKernel.certLength c0 c1 == some cert &&
  TlsMpc.ReceiveKernel.contentOk contentU cert false && messageBytes contentU cert false == msgN

/-! ## The stand-in kernels -/

/-- A stand-in circuit: an input width, and fixed output fields (mark, bits). -/
def fixed (inW : Nat) (fields : List (Mark × Bits)) : Circuit :=
  ⟨inW, fields.flatMap (fun f => List.replicate f.2.length f.1), fun _ => fields.flatMap (·.2)⟩

def nv (b : B8) : Mark × Bits := (.never, bitsOf b)
def pb (b : B8) : Mark × Bits := (.pub, bitsOf b)
def wd (n : Nat) : Mark × Bits := (.never, Conv.word n)

def prekeyFlags : B8 := b8 ([0, 0, 0, 0, 0, 0] ++ [0, 255, 0, 0, 0] ++ [255, 0, 0, 0, 0] ++ [255, 0, 0, 0, 0])
def signalFlags : B8 := b8 ([255, 0, 0, 0, 0] ++ [255, 0, 0, 0, 0] ++ [48, 0, 0])
def kyberCt : B8 := pattern 5 1568
def ids : B8 := b8 [0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 9]
def hello : B8 := b8 [104, 101, 108, 108, 111]
def conversation : B8 := pattern 8 (ownCert + contactBytes)

/-- The stand-in for one receive kernel, by its name's stem and parameters. `accept`: the second
half of sealed sender is valid (else it opens `00 00`). -/
def kernelStandIn (accept : Bool) : String → List Nat → Option Circuit
  | "receive-envelope-point", [s] => some (fixed (8 * s) [wd 12345])
  | "receive-unseal-static", [s] => some (fixed (8 * s + 256 + 255) [nv [255], nv (pattern 1 32), wd 777, nv (pattern 2 32)])
  | "receive-unseal-message", [s] =>
    some (fixed (8 * s + 8 + 256 + 255) [nv (b8 [if accept then 255 else 0]), nv (zeros (TlsMpc.ReceiveKernel.contentBytes s)),
      pb (if accept then b8 [c0, c1] else zeros 2)])
  | "receive-content-shape", [u, _, _] => some (fixed (8 * u + 8) [pb (b8 [255, 0, 0, 0])])
  | "receive-content", [u, _, _, h] =>
    some (fixed (8 * u + 8) [nv (b8 [255]), nv (b8 [1]), nv (pattern 3 cert), nv (zeros (messageBytes u cert (h == 1)))])
  | "receive-certificate", [_, _, _, _] =>
    some (fixed (8 * cert + 8 + 256 + 8 * cshape.signerSize + 64 + 255 + 255)
      [nv (b8 [255]), nv (pattern 4 16), nv (b8 [5]), nv (pattern 6 64), (.never, [true]),
       (.never, bitsOf (pattern 7 32)), (.never, (bitsOf (pattern 9 32)).take 253)])
  | "receive-certificate-verified", [] => some (fixed (8 + 512 + 3 * 255) [nv (b8 [255])])
  | "receive-prekey-shape", [n] => some (fixed (8 * n + 8) [pb prekeyFlags])
  | "receive-prekey-open", [n, _, _, _, _] =>
    some (fixed (8 * n + 8 + 8 + 256) [nv (b8 [255]), wd 4242, wd 4343, pb (ids.take 4), pb ((ids.drop 4).take 4),
      pb (ids.drop 8), pb kyberCt])
  | "receive-signal-shape", [n, _, _, _, _] => some (fixed (8 * n + 8) [pb signalFlags])
  | "receive-session", [c, n, one, _, _, _, _, _, lo, hi, _, _] =>
    let q := if hi = 0 then lo else lo % 128 + 128 * hi
    some (fixed (8 * n + 8 + 8 + 256 + 256 + 136 + 128 + 8 + 3 * 255 + (if one > 0 then 255 else 0) + 256 + 6 * 255 +
      8 * c + 128 + 64)
      [pb (b8 [255]), nv (pattern 10 (c + 319)), nv (zeros receiverBytes), nv (pattern 11 (8 + q))])
  | "receive-text", [q, cp] =>
    some (fixed (8 * (8 + q)) [pb (b8 [255]), pb (b8 [0, 5]), pb (hello ++ zeros (cp - 5)), pb (b8 [255, 0, 0])])
  | "receive-access-key", [c, q, _] =>
    some (fixed (8 * (c + 319) + 8 * (8 + q)) [pb (b8 [255]), nv conversation])
  | _, _ => none

def nameString (n : Bytes) : String := String.ofList (n.map fun b => Char.ofNat b.toNat)

def circuitTable : List (String × Circuit) :=
  [("into-field-open", Conv.intoFieldOpenC), ("modadd", Conv.modaddC), ("xor-bit-open", Conv.xorBitOpenC)]

def circuitOf (accept : Bool) (n : Bytes) : Option Circuit :=
  match circuitTable.find? (fun e => ascii e.1 == n) with
  | some e => some e.2
  | none =>
    match (nameString n).splitOn " " with
    | stem :: args => (args.mapM String.toNat?).bind (kernelStandIn accept stem)
    | [] => none

/-! ## The stand-in programs -/

def checkP : Program :=
  { inputs := 512, masks := 1, rows := (List.range 512).map Row.input ++ [.div 0 1 0],
    outputs := [(512, .never), (0, .never)] }
def recoverP : Program :=
  { inputs := 1, masks := 0, rows := [.input 0, .const 1], outputs := [(1, .never), (0, .never), (0, .never)] }
def torsionP : Program :=
  { inputs := 2, masks := 0, rows := [.input 0, .input 1, .const 0], outputs := [(2, .never), (2, .never)] }

def progTable : List (String × Program) :=
  [("xeddsa-check", checkP), ("xeddsa-recover", recoverP), ("receive-torsion", torsionP),
   ("field-mask-sub", Conv.maskSub)]

def env (accept : Bool) : Env :=
  { circuits := circuitOf accept, hash := sha256,
    programs := fun n => (progTable.find? (fun e => ascii e.1 == n)).map (·.2) }

/-! ## The stand-in curve and pool -/

/-- S11 STAND-IN: party A inputs each agreement word (store bit slot `900 + position from the end`). -/
def agreeStandIn : List Job → Gen (List BoolH)
  | [] => pure []
  | _ :: js => do
    let h ← inputA (900 + js.length) 255
    let hs ← agreeStandIn js
    pure (h :: hs)

theorem agreeStandIn_reveals : ∀ (js : List Job) (st : St), Reveals [] (agreeStandIn js st)
  | [], _ => Every.done _
  | _ :: js, st =>
    (RevealsG.bind (inputA_reveals _ _) fun _ =>
      RevealsG.bind (fun st => agreeStandIn_reveals js st) fun _ => RevealsG.pure _) st

/-- `xeddsa-check`'s one mask; its contributions are in slot 800, which op 50 takes from the supply
(J1, `Receive.Gen.takeSlot`). -/
def pm : ProgramMasks := { check := 1 }

def curve : Curve := Curve.withPrograms agreeStandIn [] agreeStandIn_reveals pm

def poolWords : Nat := 12
def poolBits : Nat := 510

/-- A's word-mask values and bit-pair bits (stand-in pool). -/
def maskVal (j : Nat) : Nat := 1000003 * (j + 1) + 17
def pairBit (j : Nat) : Bool := j % 3 == 1

/-- STAND-IN POOL: party A inputs consistent word masks (word bits and the field element) and bit
pairs; party B inputs zero field elements. Not cut-and-choose. -/
def poolScript : Gen Unit := do
  for j in List.range poolWords do
    let n ← Gen.allocB 1
    let f ← Gen.allocF 2
    Gen.instrs [.boolInput ⟨n⟩ .a 255 false false (600 + j), .fieldInput [⟨f⟩] [⟨f + 1⟩] .elements false (600 + j),
      .freeField ⟨f + 1⟩]
    modify fun st => { st with pool := { st.pool with words := st.pool.words ++ [⟨⟨n⟩, ⟨f⟩⟩] } }
  let n ← Gen.allocB (1 + poolBits)
  let f ← Gen.allocF (2 * poolBits)
  Gen.instrs ([.boolInput ⟨n⟩ .a poolBits false false 700,
    .fieldInput (fieldRange f poolBits) (fieldRange (f + poolBits) poolBits) .elements false 700] ++
    (List.range poolBits).map (fun j => (.slice ⟨n + 1 + j⟩ ⟨n⟩ j (j + 1) : Instr)) ++
    [.freeBool ⟨n⟩] ++ freeFieldsI (fieldRange (f + poolBits) poolBits))
  modify fun st => { st with pool := { st.pool with
    bits := (List.range poolBits).map fun j => ⟨⟨n + 1 + j⟩, ⟨f + j⟩⟩ } }

/-! ## The stores -/

def fi : FirstIn :=
  { ours := pattern 12 32, now := b8 [0, 0, 1, 2, 3, 4, 5, 6], serverX := 9, serverY := 1234567,
    signerCertificate := [], signerId := pattern 13 cshape.signerSize }

def envelope : B8 := pattern 14 envSize

def storeA : Store :=
  { bits := fun j =>
      if 600 ≤ j ∧ j < 600 + poolWords then Conv.word (maskVal (j - 600))
      else if j = 700 then (List.range poolBits).map pairBit
      else if 900 ≤ j ∧ j < 910 then Conv.word (5000 + j)
      else if j = 710 then bitsOf (pattern 15 32)
      else if j = 720 then bitsOf (pattern 16 ownCert)
      else [],
    elems := fun j =>
      if 600 ≤ j ∧ j < 600 + poolWords then [fe (maskVal (j - 600))]
      else if j = 700 then (List.range poolBits).map fun k => if pairBit k then fe 1 else fe 0
      else if j = 800 then [fe 77]
      else [] }

def storeB : Store :=
  { elems := fun j =>
      if 600 ≤ j ∧ j < 600 + poolWords then [fe 0]
      else if j = 700 then List.replicate poolBits (fe 0)
      else if j = 800 then [fe 88]
      else [] }

/-! ## Batches, the functionality with its evaluations listed -/

def emitBatch (E : Env) (c : Ctx) (b : List Wire) : Ctx × List String :=
  let lines := [s!"batch {hex (encodeBatch b)}"]
  match checkBatch E.sigs c (b.map InstrP.skel) with
  | .ok (c', _) => (c', lines ++ ["verdict ok"])
  | .error i => (c, lines ++ [s!"verdict refused {i}"])

def evals (E : Env) (w : Wire) (I : Ideal) : List String :=
  match w with
  | .run _ name copies input =>
    match E.circuits name, I.bools input.id with
    | some c, some v =>
      (List.range copies).map fun j =>
        let x := (v.drop (j * c.inWidth)).take c.inWidth
        s!"eval {hex name} {hexBits x} {hexBits (c.eval x)}"
    | _, _ => []
  | _ => []

def sigsUsed (E : Env) (w : Wire) : List String :=
  match w with
  | .run _ name _ _ =>
    match E.circuits name with
    | some c => [s!"sig {hex name} {c.inWidth} {String.join (c.outMarks.map markCode)}"]
    | none => []
  | _ => []

def runWiresLog (E : Env) : List Wire → List Wire → Ideal → Option (Ideal × List Release × List Release × List String)
  | [], [], I => some (I, [], [], [])
  | wA :: as, wB :: bs, I =>
    match idealStep E .a wA wB.part I with
    | some (I', toA, toB) =>
      match runWiresLog E as bs I' with
      | some (I'', ra, rb, ev) => some (I'', toA.toList ++ ra, toB.toList ++ rb, evals E wA I ++ sigsUsed E wA ++ ev)
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

def runPair (E : Env) {α : Type} : Nat → Script α → Script α → Run → Run × Option (α × α)
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
        match runWiresLog E ba.wires bb.wires r.I with
        | none => ({ r with lines := r.lines ++ ["error functionality"] }, none)
        | some (I', relA, relB, ev) =>
          let ea := emitBatch E r.ca ba.wires
          let eb := emitBatch E r.cb bb.wires
          let lines := ["round", "party a"] ++ ea.2 ++ [s!"reply {hex (encodeReplies (relA.map (·.datum)))}"] ++
            ["party b"] ++ eb.2 ++ [s!"reply {hex (encodeReplies (relB.map (·.datum)))}"]
          let r' := { r with ca := ea.1, cb := eb.1, I := I', lines := r.lines ++ lines, evals := r.evals ++ ev }
          match ra0, rb0 with
          | .finished x, .finished y => (r', some (x, y))
          | .waiting ia ka, .waiting ib kb =>
            let rA := absorb sha256 .a ia r.σA (if ia.releasesTo .a then relA.getLast? else none)
            let rB := absorb sha256 .b ib r.σB (if ib.releasesTo .b then relB.getLast? else none)
            runPair E fuel (ka rA.1) (kb rB.1) { r' with σA := rA.2, σB := rB.2 }
          | _, _ => ({ r' with lines := r'.lines ++ ["error shape"] }, none)

/-- Run one state-threaded script on both parties (the same script: its private data are slots). -/
def step {α : Type} (E : Env) (r : Run) (st : St) (g : Gen α) : Run × Option (α × St) :=
  let (r', res) := runPair E 400 (g st) (g st) r
  (r', res.map (·.1))

def bitsAt (r : Run) (h : BoolH) : Bits := (r.I.bools h.id).getD []

def check (name : String) (ok : Bool) : String := s!"check {name} {if ok then "ok" else "FAIL"}"

def main : IO Unit := do
  IO.println (check "parameters" paramsOk)
  -- J21: the receiver record's width the session script slices by (`Receive.receiverBytes`); the layout
  -- checks (`e2e_s14.py`, `loader.rs` `RECEIVER_BYTES`) read it from this line.
  IO.println s!"layout receive-session receiver {receiverBytes}"
  IO.println s!"info cert {cert} n {msgN} u {contentU} size {envSize} certLength {TlsMpc.ReceiveKernel.certLength c0 c1} contentOk {TlsMpc.ReceiveKernel.contentOk contentU cert false} msg {messageBytes contentU cert false}"
  for (name, p) in progTable do
    IO.println s!"prog {hex (ascii name)} {hex (ascii (TlsMpc.FieldDag.V3.render p))}"
  let E := env true
  let r0 : Run := { σA := storeA, σB := storeB, ca := { progs := E.progs }, cb := { progs := E.progs }, I := {},
                    lines := ["flow s14-receive"], evals := [] }
  let st0 : St := {}
  -- the stand-in pool
  let (r, p) := step E r0 st0 poolScript
  let some (_, st) := p | IO.println "error pool"
  -- the envelope's bytes as a revealed buffer (public bits, as tls-reveal-masked's are public)
  let (r, b) := step E r st (publicBits (bitsOf envelope))
  let some (buf, st) := b | IO.println "error buffer"
  -- op 48 twice (two records), op 50, op 51
  let (r, t1) := step E r st (takeScript none buf 0 100)
  let some (h1, st) := t1 | IO.println "error take"
  let (r, t2) := step E r st (takeScript (some h1) buf 100 (envSize - 100))
  let some ((envH, size), st) := t2 | IO.println "error take 2"
  let (r, o) := step E r { st with slots := [(800, 1)] } (openFirst curve (fun _ => true) fi envH size)
  let some (res, st) := o | IO.println "error open"
  let some ((oneTime, opened), arrival) := res | IO.println "error refused"
  let certH := (st.table.ctr.bool)
  let (r, c) := step E r st (inputA 720 (8 * ownCert))
  let some (account, st) := c | IO.println "error account"
  let ss : SessionSecrets := ⟨account, ownCert, 1, 2, 710, 3⟩
  let sp : SessionPublic := { address := pattern 17 17, requestId := b8 [128, 0, 0, 0, 0, 0, 0, 0], jump := 0 }
  let (r, s) := step E r st (session curve (fun _ => true) arrival sp ss)
  let some (res2, st) := s | IO.println "error session"
  let some (text, record) := res2 | IO.println "error session refused"
  -- a second envelope, refused at the certificate length (stand-in: the second half invalid)
  let E2 := env false
  let (r, b2) := step E2 r st (publicBits (bitsOf (pattern 19 envSize)))
  let some (buf2, st) := b2 | IO.println "error buffer 2"
  let (r, t3) := step E2 r st (takeScript none buf2 0 envSize)
  let some ((env2, size2), st) := t3 | IO.println "error take 3"
  let (r, o2) := step E2 r st (openFirst curve (fun _ => true) fi env2 size2)
  let some (res3, _) := o2 | IO.println s!"error open 2 {(r.lines.drop (r.lines.length - 3))}"
  for e in r.evals.eraseDups do IO.println e
  for l in r.lines do IO.println l
  IO.println "finished"
  IO.println "endflow"
  IO.println (check "opened" (!oneTime && opened == ids ++ kyberCt))
  IO.println (check "text" (text == hello))
  IO.println (check "record" (bytesOf (bitsAt r record) == (conversation.drop ownCert).take contactBytes))
  IO.println (check "refused" res3.isNone)
  IO.println s!"info cert {cert} n {msgN} u {contentU} size {envSize} certHandle {certH}"

end S14V

def main : IO Unit := S14V.main
