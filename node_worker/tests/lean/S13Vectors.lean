import TlsMpc.Node.Flows.SendProofs
import TlsMpc.Sha256

/-!
Test vectors of the S13 send flows for the stand-in two-party test `node_worker/tests/s13_pair.rs`,
computed by the Lean model itself (`Engine/Model.lean` `idealStep` on each agreed batch) from the
Lean scripts (`Flows/Send.lean`). Not part of the library; nothing imports it.

    lake env lean --run node_worker/tests/lean/S13Vectors.lean      # stdout → node_worker/tests/s13_vectors.txt

Two flows, with small parameters (an 8-byte certificate, a built text of one size class):
  * `s13-send`: op 41 (`Send.sealScript`: widths, the seal kernel, the status, timestamp ‖ envelope),
    op 42 (`Send.requestScript`), and the request's record phase (`Send.requestCtrScript` on the frame
    `Send.frameFor` builds from the opened envelope and timestamp);
  * `s13-devices`: op 61 with two devices (`Send.devicesScript`), op 62 (`requestDevicesScript`) and
    the record phase with `bundle-request-ctr` on `PublicRequest.buildDevices`' frame.
The tag phase is S12's `Tls.tagScript` (tested by s12_pair.rs).

STAND-IN CIRCUITS. `signal-widths` is the Lean kernel itself (`Contacts.kernelCircuit`); the seal
and request kernels are their SPECIFICATIONS on concrete bytes (`SealSend.sealValue`, the right-hand
sides of `signalRequestCtr_spec` / `bundleRequestCtr_spec`), equal to the kernels by `seal_out` /
`signalSeal_value` and those theorems. Every evaluation is listed (`eval` lines).

TEST STATE (a `Config.test` deviation): the account's certificate, the contact's records, the words
(sender key, static and ephemeral agreements) and the traffic block are party A's private inputs
(S11 makes the words in the deployment).

Format: as s12_vectors.txt (`sig`, `eval`, `flow` … `endflow` with rounds, `check NAME ok|FAIL`).
-/

open TlsMpc.Node
open TlsMpc.Node.Engine
open TlsMpc.Node.Flows
open TlsMpc.Node.Flows.Contacts (bitsOf bytesOf B8 kernelCircuit)
open TlsMpc TlsMpc.Signal

namespace S13V

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

/-! ## Parameters -/

def cert : Nat := 8
def classes : Nat := 1
def official : Bool := false
def content : Nat := KernelSpecs.SealFixed.contentBytes classes official
def textLen : Nat := Send.textBytes classes official

/-! ## The stand-in circuits -/

def specC (inBits : Nat) (marks : List Mark) (f : Bits → B8) : Circuit := ⟨inBits, marks, fun v => bitsOf (f v)⟩

/-- A 255-bit word's 32 bytes as the kernel reads them (`HybridKdf.wordBytes`: the top bit 0). -/
def wordOf (w : Bits) : B8 := bytesOf (w.take 255 ++ [false])

def sealSpec (cw pw ew iw : Nat) (v : Bits) : B8 :=
  let C := Send.convBytes cert
  let conv := bytesOf (v.take (8 * C))
  let text := bytesOf ((v.drop (8 * C)).take (8 * textLen))
  let w := v.drop (8 * C + 8 * textLen)
  let word := fun k => wordOf (w.drop (255 * k))
  (KernelSpecs.SealSend.sealValue cert cw pw ew iw content conv text (word 0) (word 1) (word 2) (word 3)).flatten

def requestSpec (size u k d g : Nat) (v : Bits) : B8 :=
  let b := bytesOf v
  let C := Send.convBytes cert
  let K := b.take 60
  let seqB := (b.drop 60).take 8
  let conv := (b.drop 68).take C
  let frame := (b.drop (68 + C)).take size
  let mask := (b.drop (68 + C + size)).take 4
  let slots := KernelSpecs.signalRequestSlots cert u k d g conv
  (KernelSpecs.sealedRequest K seqB (KernelSpecs.insertSlots ByteAuth.concrete 0 frame mask 8 slots.2) slots.1).flatten

def bundleRequestSpec (size payloadAt u k : Nat) (devices : List (Nat × Nat)) (v : Bits) : B8 :=
  let b := bytesOf v
  let R := Send.recordBytes * devices.length
  let K := b.take 60
  let seqB := (b.drop 60).take 8
  let records := (b.drop 68).take R
  let frame := (b.drop (68 + R)).take size
  let mask := (b.drop (68 + R + size)).take 4
  let value := KernelSpecs.bundleRequestValue records u k devices
  (KernelSpecs.sealedRequest K seqB (KernelSpecs.insertSlots ByteAuth.concrete 0 frame mask payloadAt value.2)
    value.1).flatten

def requestMarks (size : Nat) : List Mark :=
  List.replicate (8 * (1 + 5 + Send.innerOf size)) .pub ++ List.replicate 128 .never

/-- The model's circuit by name (the names the scripts use). -/
def circuitOf (name : String) : Option Circuit :=
  match (name.splitOn " ").map (fun s => (s, s.toNat?)) with
  | [("signal-widths", _), (_, some c)] =>
    if c = cert then some (kernelCircuit (HybridKernel.signalWidths cert) (Send.convBytes cert) (List.replicate 168 .pub))
    else none
  | [("signal-seal-built", _), (_, some c), (_, some cl), (_, some cw), (_, some pw), (_, some ew), (_, some iw)] =>
    if c = cert ∧ cl = classes then
      let E := Send.sealEnvBytes cert classes false cw pw ew iw
      some (specC (8 * Send.convBytes cert + 8 * textLen + 4 * 255) (Send.sealMarks cert E) (sealSpec cw pw ew iw))
    else none
  | [("signal-request-ctr", _), (_, some c), (_, some size), (_, some u), (_, some k), (_, some d), (_, some g)] =>
    if c = cert then some (specC (8 * (68 + Send.convBytes cert + size + 4)) (requestMarks size) (requestSpec size u k d g))
    else none
  | ("bundle-request-ctr", _) :: (_, some size) :: (_, some pa) :: (_, some u) :: (_, some k) :: rest =>
    match BundleKernel.pairs (rest.filterMap (·.2)) with
    | some ds =>
      some (specC (8 * (68 + Send.recordBytes * ds.length + size + 4)) (requestMarks size)
        (bundleRequestSpec size pa u k ds))
    | none => none
  | _ => none

def nameOf (b : Bytes) : String := String.ofList (b.map fun x => Char.ofNat x.toNat)

def env : Env := { circuits := fun n => circuitOf (nameOf n), hash := sha256 }

/-! ## Batches, the functionality with its evaluations listed (as S12Vectors) -/

def emitBatch (c : Ctx) (b : List Wire) : Ctx × List String :=
  let lines := [s!"batch {hex (encodeBatch b)}"]
  match checkBatch env.sigs c (b.map InstrP.skel) with
  | .ok (c', _) => (c', lines ++ ["verdict ok"])
  | .error i => (c, lines ++ [s!"verdict refused {i}"])

/-- The circuit evaluations of one agreed instruction, and the circuit names used. -/
def evals (w : Wire) (I : Ideal) : List String × List String :=
  match w with
  | .run _ name copies input =>
    match env.circuits name, I.bools input.id with
    | some c, some v =>
      ((List.range copies).map fun j =>
        let x := (v.drop (j * c.inWidth)).take c.inWidth
        s!"eval {hex name} {hexBits x} {hexBits (c.eval x)}", [nameOf name])
    | _, _ => ([], [])
  | _ => ([], [])

def runWiresLog : List Wire → List Wire → Ideal →
    Option (Ideal × List Release × List Release × List String × List String)
  | [], [], I => some (I, [], [], [], [])
  | wA :: as, wB :: bs, I =>
    match idealStep env .a wA wB.part I with
    | some (I', toA, toB) =>
      match runWiresLog as bs I' with
      | some (I'', ra, rb, ev, ns) => some (I'', toA.toList ++ ra, toB.toList ++ rb, (evals wA I).1 ++ ev,
          (evals wA I).2 ++ ns)
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
  names : List String

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
        | some (I', relA, relB, ev, ns) =>
          let ea := emitBatch r.ca ba.wires
          let eb := emitBatch r.cb bb.wires
          let lines := ["round", "party a"] ++ ea.2 ++ [s!"reply {hex (encodeReplies (relA.map (·.datum)))}"] ++
            ["party b"] ++ eb.2 ++ [s!"reply {hex (encodeReplies (relB.map (·.datum)))}"]
          let r' : Run := ⟨r.σA, r.σB, ea.1, eb.1, I', r.lines ++ lines, r.evals ++ ev, r.names ++ ns⟩
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

/-! ## The scenario's values -/

def bytesN (seed n : Nat) : B8 := (List.range n).map fun i => BitVec.ofNat 8 (seed * 131 + i * 29 + 7)

def certB : B8 := bytesN 1 cert
def senderKey : B8 := (bytesN 2 31) ++ [BitVec.ofNat 8 0x31]   -- top bit clear: a 255-bit word

/-- A live record (319 bytes): version 4, counter 0, previous 0, ratchet, chain key, SPQR chain key,
SPQR counter 0, epoch 1, kind 0, our sender key, the recipient key, the plaintext slot; metadata:
UUID 16, access key 16, …, device id 1 (byte 48), registration id 1234 (bytes 49-52). -/
def record (seed : Nat) : B8 :=
  [4] ++ List.replicate 4 0 ++ List.replicate 4 0 ++ bytesN (seed + 3) 32 ++ bytesN (seed + 4) 32 ++
    bytesN (seed + 5) 32 ++ List.replicate 4 0 ++ (List.replicate 7 0 ++ [1]) ++ [0] ++ senderKey ++
    bytesN (seed + 6) 32 ++ List.replicate 80 0 ++
    (bytesN (seed + 7) 16 ++ bytesN (seed + 8) 16 ++ List.replicate 16 0 ++ [1] ++ [0, 0, 4, 210] ++
      List.replicate 4 0)

def timestamp : B8 := [0, 0, 1, 146, 100, 200, 30, 40]
/-- A built text of class 1: validity 255, kind 0, 80 content bytes, the timestamp. -/
def builtText : B8 := [255, 0] ++ [104, 105] ++ List.replicate 78 0 ++ timestamp

def wordBits (b : B8) : Bits := (bitsOf b).take 255

def traffic : B8 := bytesN 9 60
def seqB : B8 := List.replicate 8 0
def mask : B8 := [17, 34, 51, 68]

def putBits (σ : Store) (slot : Nat) (b : Bits) : Store := σ.setBits slot b

/-- Party A's private inputs (owner A), one handle each, from store slots `slot …`. -/
def inputsScript (n slot : Nat) (widths : List Nat) : Script Unit :=
  Contacts.seqs ((List.range widths.length).zip widths |>.map fun (i, w) =>
    InstrP.boolInput ⟨n + i⟩ .a w false false (slot + i)) (.done ())

def bitsAt (r : Run) (h : BoolH) : Bits := (r.I.bools h.id).getD []

def storeOf (a : List Bits) : Store :=
  ((List.range a.length).zip a).foldl (fun σ p => σ.setBits (1 + p.1) p.2) ({} : Store)

def run0 (name : String) (a : List Bits) : Run :=
  ⟨storeOf a, ({} : Store), ({} : Ctx), ({} : Ctx), ({} : Ideal), [s!"flow {name}"], [], []⟩

/-- The reference of `send_accepted` for one seal (sealSend's references on the concrete inputs). -/
def reference (conv : B8) (eph agr static : B8) : B8 × B8 :=
  let shape : Serialization.Shape := ⟨1, 1, false⟩
  let pqShape : SpqrMessage.Shape := ⟨1, 1, 1, false⟩
  let staged := KernelSpecs.SealFixed.stagedOf ((conv.drop cert).take (182 + 80)) builtText
  let i := KernelSpecs.SealFixed.inputOf 0 staged builtText content
  let p := SpqrSend.canonical shape pqShape i
  (KernelSpecs.SealValue.Reference.sealV1 i.receiver eph senderKey agr static (conv.take cert) p.wire,
   (KernelSpecs.SealSend.advancedRecord cert conv staged p).drop cert)

def flags (b : Bool) : String := if b then "ok" else "FAIL"

def fail (r : Run) (msg : String) : IO Unit := do
  for l in r.lines do IO.println l
  IO.println s!"error {msg}"

def main : IO Unit := do
  -- ===== flow 1: one record (op 41, op 42, the request's record phase) =====
  let rec0 := record 10
  let ephPk := bytesN 30 32
  let agr := (bytesN 31 31) ++ [5]
  let static := (bytesN 32 31) ++ [6]
  -- handles 0 cert, 1 state, 2 sender, 3 static, 4 ephemeral agreement, 5 traffic
  let r := run0 "s13-send" [bitsOf certB, bitsOf rec0, wordBits senderKey, wordBits static, wordBits agr, bitsOf traffic]
  let (r, _) := step r (inputsScript 0 1 [8 * cert, 8 * Send.recordBytes, 255, 255, 255, 480])
  let a : Send.SealArgs := ⟨⟨0⟩, cert, ⟨2⟩, ⟨3⟩, ⟨1⟩, builtText, ephPk, ⟨4⟩⟩
  let (r, sealed) := step r (Send.sealScript 10 a)
  let some (some sd) := sealed | fail r "seal (refused or aborted)"
  -- the kernel reads the public key as a 255-bit word (its top bit dropped, `wordOf`)
  let (envRef, recRef) := reference (certB ++ rec0) (wordOf (wordBits ephPk)) (wordOf (wordBits agr))
    (wordOf (wordBits static))
  let sealOk := sd.envelopes == [envRef] && sd.timestamp == timestamp && bytesOf (bitsAt r sd.state) == recRef
  let (r, conv) := step r (Send.requestScript 20 ⟨0⟩ sd.state)
  let some conv := conv | IO.println "error request"
  let env := sd.envelopes.headD []
  let some (frame, offsets) := (Send.frameFor env sd.timestamp 7 mask false).toOption | IO.println "error frame"
  let name := Send.requestNameOf cert frame offsets
  let (r, ctr) := step r (Send.requestCtrScript 30 ⟨5⟩ conv seqB frame mask name)
  let some (hc, _) := ctr | fail r "request record"
  let convNew := certB ++ recRef
  let msg := PublicRequest.sendMessage env (Send.beNat timestamp) 7 false
  let plain := KernelSpecs.RequestFrame.buildHeader (PublicRequest.total msg) mask ++
    KernelSpecs.RequestFrame.maskFrom mask 0
      (KernelSpecs.RequestFrame.render (KernelSpecs.RequestFrame.requestValues cert convNew) msg)
  let inner := TlsRecord.inner Gcm.concrete plain 23 0
  let requestOk := hc == TlsRecord.header Gcm.concrete (inner.length + 16) ++ HybridKernel.ctrOf traffic seqB inner
  for e in r.evals.eraseDups do IO.println e
  for l in r.lines do IO.println l
  IO.println "finished"
  IO.println "endflow"
  let names1 := r.names
  -- ===== flow 2: two records (op 61, op 62, the request's record phase) =====
  let rec1 := record 40
  let rec2 := record 70
  let state := rec1 ++ rec2
  let eph1 := bytesN 33 32
  let eph2 := bytesN 34 32
  let agr1 := (bytesN 35 31) ++ [7]
  let agr2 := (bytesN 36 31) ++ [8]
  let address := bytesN 37 17
  -- handles 0 cert, 1 state, 2 sender, 3 static, 4 agreement 1, 5 agreement 2, 6 traffic
  let r := run0 "s13-devices" [bitsOf certB, bitsOf state, wordBits senderKey, wordBits static, wordBits agr1,
    wordBits agr2, bitsOf traffic]
  let (r, _) := step r (inputsScript 0 1 [8 * cert, 16 * Send.recordBytes, 255, 255, 255, 255, 480])
  let da : Send.DevicesArgs := ⟨⟨0⟩, cert, ⟨2⟩, ⟨3⟩, ⟨1⟩, builtText, address,
    [⟨0, 0, eph1, ⟨4⟩⟩, ⟨0, Send.recordBytes, eph2, ⟨5⟩⟩]⟩
  let (r, sealed) := step r (Send.devicesScript 10 da)
  let some (some sd) := sealed | fail r "devices (refused or aborted)"
  let (e1, n1) := reference (certB ++ rec1) (wordOf (wordBits eph1)) (wordOf (wordBits agr1)) (wordOf (wordBits static))
  let (e2, n2) := reference (certB ++ rec2) (wordOf (wordBits eph2)) (wordOf (wordBits agr2)) (wordOf (wordBits static))
  let devicesOk := sd.envelopes == [e1, e2] && sd.timestamp == timestamp && bytesOf (bitsAt r sd.state) == n1 ++ n2
  let (r, records) := step r (Send.requestDevicesScript 40 sd.state [0, Send.recordBytes])
  let some records := records | IO.println "error request devices"
  let some (frame2, payloadAt, offsets2) := (PublicRequest.buildDevices sd.envelopes (Send.beNat timestamp) 8 mask
    false).toOption | IO.println "error devices frame"
  let some name2 := Send.devicesNameOf frame2 payloadAt offsets2 | IO.println "error devices name"
  let (r, ctr2) := step r (Send.requestCtrScript 50 ⟨6⟩ records seqB frame2 mask name2)
  let some (hc2, _) := ctr2 | fail r "devices record"
  let msg2 := PublicRequest.devicesMessage sd.envelopes (Send.beNat timestamp) 8 false
  let plain2 := KernelSpecs.RequestFrame.assembleHeader (PublicRequest.total msg2) mask ++
    KernelSpecs.RequestFrame.maskFrom mask 0
      (KernelSpecs.RequestFrame.render (KernelSpecs.RequestFrame.devicesValues (n1 ++ n2)) msg2)
  let inner2 := TlsRecord.inner Gcm.concrete plain2 23 0
  let devicesRequestOk := hc2 == TlsRecord.header Gcm.concrete (inner2.length + 16) ++
    HybridKernel.ctrOf traffic seqB inner2
  for e in r.evals.eraseDups do IO.println e
  for l in r.lines do IO.println l
  IO.println "finished"
  IO.println "endflow"
  for n in (names1 ++ r.names).eraseDups do
    match circuitOf n with
    | some c => IO.println s!"sig {hex (ascii n)} {c.inWidth} {String.join (c.outMarks.map markCode)}"
    | none => IO.println s!"error sig {n}"
  IO.println s!"check seal {flags sealOk}"
  IO.println s!"check request {flags requestOk}"
  IO.println s!"check devices {flags devicesOk}"
  IO.println s!"check devices-request {flags devicesRequestOk}"

end S13V

def main : IO Unit := S13V.main
