import TlsMpc.Node.Flows.CeremonyRun
import TlsMpc.Node.Flows.Send
import TlsMpc.Sha256

/-!
Test vectors of the S16 ceremony flows for the stand-in two-party test `node_worker/tests/s16_pair.rs`
and the real-engine fixture `node_worker/tests/e2e_s16.py`, computed by the Lean model itself
(`Engine/Model.lean` `idealStep` on each agreed batch) from the Lean scripts (`Flows/Ceremony.lean`,
`Flows/Send.lean`). Not part of the library; nothing imports it.

    lake env lean --run node_worker/tests/lean/S16Vectors.lean      # stdout → node_worker/tests/s16_vectors.txt

One flow, `s16-ceremony`: party A's traffic block (a TEST private input), op 80
(`Ceremony.secretsScript`: each party's seed, mask and recovery half; `ceremony-secrets`; the masked
password opened), op 81's engine part (`Ceremony.registerScript`: tail ‖ password ‖ recovery) and
the registration request's record phase (`Send.requestCtrScript` with `ceremony-register-ctr 5584 8
5552 1 365`, the shape of the kernel the cache holds from the C++ ceremony; a frame of 5584 bytes with
zero bytes at its two slots). The tag phase is S12's `Tls.tagScript` (tested by s12_pair.rs).

STAND-IN CIRCUITS: `ceremony-secrets` is its reference (`Ceremony.secrets` on concrete bytes; the
kernel computes it: `ceremonySecrets_spec`); `ceremony-register-ctr` is the right-hand side of
`Ceremony.ceremonyRegisterCtr_spec` (`KernelSpecs.sealedRequest` of `Ceremony.fill`). The real
kernels compute the same functions, so the real-engine fixture compares the replies byte for byte.
Every evaluation is listed (`eval` lines).

Checks (`check NAME ok|FAIL`): `masked` (the opened value is the reference's third field),
`shares` (the two parties' replies, `shareOf`, XOR to password ‖ recovery: `shares_xor`), `secrets`
(op 81's handle holds tail ‖ password ‖ recovery: `register_honest`), `request` (the opened header ‖
ciphertext is the TLS record of the filled frame: `registerCtr_value`).

Format: as s13_vectors.txt (`sig`, `eval`, `flow` … `endflow` with rounds, `check NAME ok|FAIL`).
-/

open TlsMpc.Node
open TlsMpc.Node.Engine
open TlsMpc.Node.Flows
open TlsMpc.Node.Flows.Contacts (bitsOf bytesOf B8)
open TlsMpc TlsMpc.Signal

namespace S16V

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

/-! ## Parameters: the shape of the cached `ceremony-register-ctr 5584 8 5552 1 365` -/

def size : Nat := 5584
def payloadAt : Nat := 8
def authAt : Nat := 5552
def recoveryAt : Nat := 365

/-! ## The stand-in circuits -/

def specC (inBits : Nat) (marks : List Mark) (f : Bits → B8) : Circuit := ⟨inBits, marks, fun v => bitsOf (f v)⟩

def secretsSpec (v : Bits) : B8 :=
  let b := bytesOf v
  (TlsMpc.Ceremony.secrets ByteAuth.concrete (b.take 18) ((b.drop 18).take 18) ((b.drop 36).take 22)
    ((b.drop 58).take 22) ((b.drop 80).take 32) ((b.drop 112).take 32)).flatten

def registerSpec (sz pa au tl rv : Nat) (v : Bits) : B8 :=
  let b := bytesOf v
  let K := b.take 60
  let seqB := (b.drop 60).take 8
  let secrets := (b.drop 68).take (tl + 54)
  let frame := (b.drop (68 + tl + 54)).take sz
  let mask := (b.drop (68 + tl + 54 + sz)).take 4
  (KernelSpecs.sealedRequest K seqB
    (TlsMpc.Ceremony.fill ByteAuth.concrete frame mask pa
      (TlsMpc.Ceremony.registerSlots ByteAuth.concrete secrets tl au rv)) 255).flatten

def requestMarks (sz : Nat) : List Mark :=
  List.replicate (8 * (1 + 5 + Send.innerOf sz)) .pub ++ List.replicate 128 .never

/-- The model's circuit by name (the names the scripts use). -/
def circuitOf (name : String) : Option Circuit :=
  match (name.splitOn " ").map (fun s => (s, s.toNat?)) with
  | [("ceremony-secrets", _)] => some (specC (8 * Ceremony.inputBytes) Ceremony.secretsMarks secretsSpec)
  | [("ceremony-register-ctr", _), (_, some sz), (_, some pa), (_, some au), (_, some tl), (_, some rv)] =>
    some (specC (8 * (68 + tl + 54 + sz + 4)) (requestMarks sz) (registerSpec sz pa au tl rv))
  | _ => none

def nameOf (b : Bytes) : String := String.ofList (b.map fun x => Char.ofNat x.toNat)

def env : Env := { circuits := fun n => circuitOf (nameOf n), hash := sha256 }

/-! ## Batches, the functionality with its evaluations listed (as S13Vectors) -/

def emitBatch (c : Ctx) (b : List Wire) : Ctx × List String :=
  let lines := [s!"batch {hex (encodeBatch b)}"]
  match checkBatch env.sigs c (b.map InstrP.skel) with
  | .ok (c', _) => (c', lines ++ ["verdict ok"])
  | .error i => (c, lines ++ [s!"verdict refused {i}"])

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

def step {α : Type} (r : Run) (s : Script α) : Run × Option (α × α) :=
  runPair 64 s s r

/-! ## The scenario's values -/

def bytesN (seed n : Nat) : B8 := (List.range n).map fun i => BitVec.ofNat 8 (seed * 131 + i * 29 + 7)

def seedA : B8 := bytesN 1 18
def seedB : B8 := bytesN 2 18
def maskA : B8 := bytesN 3 22
def maskB : B8 := bytesN 4 22
def recoveryA : B8 := bytesN 5 32
def recoveryB : B8 := bytesN 6 32
def traffic : B8 := bytesN 9 60
def seqB : B8 := [0, 0, 0, 0, 0, 0, 0, 3]
def mask : B8 := [17, 34, 51, 68]
/-- The public tail of `NUMBER:` (one byte, the shape's TAIL). -/
def tail : B8 := [0x3a]

/-- A frame of 5584 bytes built "in the clear": arbitrary public bytes, zero at the two slots. -/
def frame : B8 := (List.range size).map fun i =>
  if (authAt ≤ i ∧ i < authAt + 32) ∨ (recoveryAt ≤ i ∧ i < recoveryAt + 44) then 0
  else BitVec.ofNat 8 ((i * 37 + 11) % 251)

def storeOf (a : List (Nat × Bits)) : Store := a.foldl (fun σ p => σ.setBits p.1 p.2) ({} : Store)

def bitsAt (r : Run) (h : BoolH) : Bits := (r.I.bools h.id).getD []

def flags (b : Bool) : String := if b then "ok" else "FAIL"

def fail (r : Run) (msg : String) : IO Unit := do
  for l in r.lines do IO.println l
  IO.println s!"error {msg}"

def main : IO Unit := do
  let σA := storeOf [(1, bitsOf seedA), (2, bitsOf maskA), (3, bitsOf recoveryA), (4, bitsOf traffic)]
  let σB := storeOf [(1, bitsOf seedB), (2, bitsOf maskB), (3, bitsOf recoveryB)]
  let r : Run := ⟨σA, σB, ({} : Ctx), ({} : Ctx), ({} : Ideal), ["flow s16-ceremony"], [], []⟩
  -- handle 0: A's traffic block (TEST private input, as S13's vectors)
  let (r, _) := step r (Contacts.seqs [.boolInput ⟨0⟩ .a 480 false false 4] (.done ()))
  -- op 80 (ids 10 … 20)
  let (r, made) := step r (Ceremony.secretsScript 10 1 2 3)
  let some (mA, mB) := made | fail r "secrets"
  let ref := Ceremony.reference seedA seedB maskA maskB recoveryA recoveryB
  let pw := ref.getD 0 []
  let rc := ref.getD 1 []
  let maskedOk := mA.masked == ref.getD 2 [] && mB.masked == ref.getD 2 []
  let shareA := Ceremony.shareOf .a maskA recoveryA mA.masked
  let shareB := Ceremony.shareOf .b maskB recoveryB mB.masked
  let sharesOk := List.zipWith (· ^^^ ·) shareA shareB == pw ++ rc && bytesOf (bitsAt r mA.password) == pw &&
    bytesOf (bitsAt r mA.recovery) == rc
  -- op 81's engine part (ids 30, 31)
  let (r, conv) := step r (Ceremony.registerScript 30 mA.password mA.recovery tail)
  let some (conv, _) := conv | fail r "register"
  let secretsOk := bytesOf (bitsAt r conv) == tail ++ (pw ++ rc)
  -- the registration request's record phase (ids 40 … 45)
  let name := Ceremony.registerName size payloadAt authAt tail.length recoveryAt
  let (r, ctr) := step r (Send.requestCtrScript 40 ⟨0⟩ conv seqB frame mask name)
  let some ((hc, _), _) := ctr | fail r "request record"
  let plain := TlsMpc.Ceremony.fill ByteAuth.concrete frame mask payloadAt
    [(authAt, RelayEncoding.base64 ByteAuth.concrete (tail ++ pw)), (recoveryAt, RelayEncoding.base64 ByteAuth.concrete rc)]
  let inner := TlsRecord.inner Gcm.concrete plain 23 0
  let requestOk := hc == TlsRecord.header Gcm.concrete (inner.length + 16) ++ HybridKernel.ctrOf traffic seqB inner
  for e in r.evals.eraseDups do IO.println e
  for l in r.lines do IO.println l
  IO.println "finished"
  IO.println "endflow"
  for n in r.names.eraseDups do
    match circuitOf n with
    | some c => IO.println s!"sig {hex (ascii n)} {c.inWidth} {String.join (c.outMarks.map markCode)}"
    | none => IO.println s!"error sig {n}"
  IO.println s!"check masked {flags maskedOk}"
  IO.println s!"check shares {flags sharesOk}"
  IO.println s!"check secrets {flags secretsOk}"
  IO.println s!"check request {flags requestOk}"

end S16V

def main : IO Unit := S16V.main
