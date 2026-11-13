import TlsMpc.Node.Flows.Select
import TlsMpc.Node.Flow

/-!
The script RUNNER (`TlsMpc/Node/Flows/Runner.lean`) and the selection (`Flows/Select.lean`) driven
end to end against a FAKE WORKER PAIR, with no engine: both parties' controllers run in two threads,
each with its own runner and flow context; their pipes meet in `Pair`, which answers operation 93
exactly as the two shells do in the model (`Engine/Model.lean` `shellPair`: the agreement on the
skeleton bytes, then `idealStep` on every instruction), after the handle table's `checkBatch`
(Engine.lean `check`, D8) has admitted each party's batch. Nothing is hand-written: every batch is
the runner's (`nextBatch` on its store), every flow is called as the session calls it (the legacy
flow function, which consults the override the selection installed).

    lake env lean --run node_worker/tests/lean/RunnerTest.lean      # prints check lines; all must be ok

STAND-INS (no kernel is evaluated): `contact-key`, `contact-seal N`, `contact-open N` are stand-in
circuits with the kernels' widths and marks (key = shareA ⊕ shareB, then zeros; a XOR "cipher" with a
check value) so a key → open → seal → open round trip and a refused open can be checked against the
stand-in's own definition. What is checked is the runner (batching, the agreement, replies, the
store, the counters), the selection's dispatch and the scripts' sequencing; not the kernels.

Flows: joint randomness (`Flow.Random.joint`, override `random`: both parties get the XOR of the two
values, P-RAND (a)); the anonymous upgrade (`Flow.Upgrade.anonymous`: RFC 6455's accept of the joint
nonce, `upgrade_honest`); contacts key, load (accepted, refused with a wrong check), seal (the
stand-in's sealed blob of the loaded content), evict, re-key, assign, the state handle's value in the
model, one `Counters` for runner and table on both parties; S14's backend on the runner: op 48 then a
refused op 50 (no receive kernel loaded).

Not covered here (they need their stage's stand-in tables as a module; the S10–S15 vector files
hold them inline): mask generation with a conversion, a record seal and open, a send, an accepted
receive, a refresh. Nothing imports this file.
-/

open TlsMpc.Node
open TlsMpc.Node.Engine
open TlsMpc.Node.Flows
open TlsMpc.Node.Flows.Contacts (B8 bitsOf bytesOf)
open TlsMpc.TlsClient (M)

namespace RT

def digit (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'
def hex (bs : Bytes) : String := String.join (bs.map fun b => String.ofList [digit (b.toNat / 16), digit (b.toNat % 16)])
def check (name : String) (ok : Bool) : IO Unit := IO.println s!"check {name} {if ok then "ok" else "FAIL"}"

def toB8 (b : Bytes) : B8 := b.map fun x => BitVec.ofNat 8 x.toNat
def ofB8 (b : B8) : Bytes := b.map fun x => UInt8.ofNat x.toNat
def xorB (a b : Bytes) : Bytes := List.zipWith (· ^^^ ·) a b

/-! ## Stand-in contact kernels -/

/-- The stand-in record key: shareA ⊕ shareB, then 28 zero bytes (60 bytes). -/
def keyOf (a b : Bytes) : Bytes := xorB a b ++ List.replicate 28 0
/-- The stand-in keystream: the key, cycled. -/
def stream (key : Bytes) (n : Nat) : Bytes := (List.range n).map fun i => key.getD (i % 60) 0
/-- The stand-in check value: 16 bytes of the key mixed with the version. -/
def checkOf (key version : Bytes) : Bytes := (List.range 16).map fun i => key.getD i 0 ^^^ version.getD (i % 8) 0 ^^^ 0x5a

def sealOut (key version content : Bytes) : Bytes := xorB content (stream key content.length) ++ checkOf key version
def openOut (key version ct check : Bytes) : Bytes :=
  (if check == checkOf key version then [255] else [0]) ++ xorB ct (stream key ct.length)

def byteCircuit (inBytes : Nat) (marks : List Mark) (f : Bytes → Bytes) : Circuit :=
  ⟨8 * inBytes, marks, fun v => bitsOf (toB8 (f (ofB8 (bytesOf v))))⟩

def nameString (n : Bytes) : String := String.ofList (n.map fun b => Char.ofNat b.toNat)

def circuits (n : Bytes) : Option Circuit :=
  match (nameString n).splitOn " " with
  | ["contact-key"] => some (byteCircuit 64 Contacts.keyMarks fun v => keyOf (v.take 32) (v.drop 32))
  | ["contact-seal", s] => s.toNat?.map fun size => byteCircuit (68 + size) (Contacts.sealMarks size)
      fun v => sealOut (v.take 60) ((v.drop 60).take 8) (v.drop 68)
  | ["contact-open", s] => s.toNat?.map fun size => byteCircuit (84 + size) (Contacts.openMarks size)
      fun v => openOut (v.take 60) ((v.drop 60).take 8) ((v.drop 68).take size) (v.drop (68 + size))
  | _ => none

def sha256 (m : Bytes) : Bytes := TlsMpc.TlsWire.hash m

def env : Env := { circuits, hash := sha256 }

/-! ## The fake worker pair -/

structure PairState where
  reqA : Option Bytes := none
  reqB : Option Bytes := none
  repA : Option (Except String Bytes) := none
  repB : Option (Except String Bytes) := none
  ideal : Ideal := {}
  ctxA : Ctx := {}
  ctxB : Ctx := {}
  batches : Nat := 0

/-- Both requests present: the handle tables admit each party's batch (`checkBatch`), then the
two shells (`shellPair`: agreement, then `idealStep`), and each party's reply items. -/
def answer (E : Env) (s : PairState) (a b : Bytes) : PairState :=
  let admit (me : Party) (c : Ctx) (req : Bytes) : Except String Ctx :=
    match usableBatch me req with
    | none => .error "unusable batch"
    | some ws => match checkBatch E.sigs c (ws.map InstrP.skel) with
      | .ok (c', _) => .ok c'
      | .error i => .error s!"check refused instruction {i}"
  match admit .a s.ctxA a, admit .b s.ctxB b with
  | .ok ca, .ok cb =>
    match shellPair E a b s.ideal with
    | some (I', ra, rb) =>
      { s with reqA := none, reqB := none, ideal := I', ctxA := ca, ctxB := cb, batches := s.batches + 1,
               repA := some (.ok (encodeReplies (ra.map (·.datum)))), repB := some (.ok (encodeReplies (rb.map (·.datum)))) }
    | none => { s with reqA := none, reqB := none, repA := some (.error "rejected"), repB := some (.error "rejected") }
  | .error e, _ => { s with reqA := none, reqB := none, repA := some (.error e), repB := some (.error e) }
  | _, .error e => { s with reqA := none, reqB := none, repA := some (.error e), repB := some (.error e) }

def pairCall (E : Env) (st : IO.Ref PairState) (me : Party) (req : Bytes) : IO (Except String Bytes) := do
  st.modify fun s => if me = .a then { s with reqA := some req } else { s with reqB := some req }
  for _ in List.range 2000000 do
    let r ← st.modifyGet fun s =>
      let s := match s.reqA, s.reqB with
        | some a, some b => answer E s a b
        | _, _ => s
      match me with
      | .a => (s.repA, { s with repA := none })
      | .b => (s.repB, { s with repB := none })
    if let some rep := r then return rep
    IO.sleep 1
  return .error "fake pair: the peer never came"

def rpc (E : Env) (st : IO.Ref PairState) (me : Party) : TlsMpc.TlsWorker.Rpc where
  call op input := do
    unless op == .batch do throw s!"fake worker: operation {TlsMpc.TlsWorkerPipe.code op} is not op 93"
    ExceptT.mk (pairCall E st me input)
  authenticate _ _ _ _ _ := return true

/-- This party's deterministic "randomness": draw `k` of party `seed` (a counter per party). -/
def draw (seed k n : Nat) : Bytes := (List.range n).map fun i => UInt8.ofNat ((seed * 151 + k * 37 + i * 13 + (i * i) % 7) % 256)

def randomOf (seed : Nat) (ctr : IO.Ref Nat) (n : Nat) : IO (Secret Bytes) := do
  let k ← ctr.get
  ctr.set (k + 1)
  return Secret.hide (draw seed k n)

def agreed (names : List String) : Config.Agreed :=
  { official := false, keepRefused := false, recovery := true, prepareBatch := 32, bundleSlots := true,
    receiveJump := none, hinted := false, circuits := 0, legacyWorker := false, scripts := names }

/-- A party's flow context with the selection's overrides installed (as `Worker.startWith`, without
`Select.check`: the test also runs groups that cannot be selected in a session yet). -/
def party (E : Env) (st : IO.Ref PairState) (me : Party) (seed : Nat) (names : List String) :
    IO (Flow.Worker × Runner.Runner) := do
  let ctr ← IO.mkRef 0
  let w ← Flow.Worker.start (rpc E st me) (randomOf seed ctr)
  let r ← Runner.Runner.start w me (fun _ => true) (fun _ => none)
  let s ← Select.Session.start r (agreed names)
  return ({ w with overrides := Select.overrides s names }, r)

/-- Run both parties' actions concurrently (A in its own thread). -/
def both {α : Type} (fa fb : M α) : IO (Except String α × Except String α) := do
  let ta ← IO.asTask (prio := .dedicated) (fa.run)
  let b ← fb.run
  let a ← IO.wait ta
  match a with
  | .ok a => return (a, b)
  | .error e => return (.error s!"thread: {e}", b)

def main : IO Unit := do
  let st ← IO.mkRef ({ ctxA := {}, ctxB := {} } : PairState)
  let names := ["random", "upgrade", "contacts"]
  let (wA, rA) ← party env st .a 1 names
  let (wB, rB) ← party env st .b 2 names
  -- 1. Joint randomness (op 33 as a script): both get the XOR of the two values (P-RAND (a)).
  let (ja, jb) ← both (Flow.Random.joint wA) (Flow.Random.joint wB)
  match ja, jb with
  | .ok a, .ok b =>
    check "random-agree" (a.val == b.val)
    check "random-value" (a.val == xorB (draw 1 1 32) (draw 2 1 32))
  | .error e, _ => IO.println s!"check random FAIL {e}"
  | _, .error e => IO.println s!"check random FAIL {e}"
  check "random-op93-recorded" ((← wA.operations) == [93])
  -- 2. The anonymous upgrade (op 45 as a script): nonce = the first 16 bytes of the joint value,
  -- accept = RFC 6455's (WebSocketAccept.upgradePublic, upgrade_honest).
  let (ua, ub) ← both (Flow.Upgrade.anonymous wA) (Flow.Upgrade.anonymous wB)
  match ua, ub with
  | .ok a, .ok b =>
    let nonce := (xorB (draw 1 3 32) (draw 2 3 32)).take 16
    let expected := TlsMpc.Local.WebSocketAccept.upgradePublic (nonce.map Upgrade.toBV)
    check "upgrade-agree" (a.val == b.val)
    check "upgrade-value" (match expected with
      | .ok reply => a.val.1 ++ a.val.2 == reply.map Upgrade.toU8
      | .error _ => false)
  | .error e, _ => IO.println s!"check upgrade FAIL {e}"
  | _, .error e => IO.println s!"check upgrade FAIL {e}"
  -- 3. Contacts (ops 36, 37, 38, 40, 52 as scripts, on the runner's table and counters).
  let shareA := draw 9 0 32
  let shareB := draw 10 0 32
  let key := keyOf shareA shareB
  let content := draw 11 0 319
  let v1 := [0, 0, 0, 0, 0, 0, 0, 1]
  let blob1 := sealOut key v1 content
  let stored1 := v1 ++ blob1.drop 319 ++ blob1.take 319
  let (ka, kb) ← both (Flow.Contacts.key wA 7 (Secret.hide shareA)) (Flow.Contacts.key wB 7 (Secret.hide shareB))
  check "contact-key" (ka matches .ok _ && kb matches .ok _)
  let (la, lb) ← both (Flow.Contacts.load wA 7 stored1) (Flow.Contacts.load wB 7 stored1)
  check "contact-load-accepted" (match la, lb with | .ok a, .ok b => a.val && b.val | _, _ => false)
  let v2 := [0, 0, 0, 0, 0, 0, 0, 2]
  let (sa, sb) ← both (Flow.Contacts.seal wA 7 v2) (Flow.Contacts.seal wB 7 v2)
  let blob2 := sealOut key v2 content
  check "contact-seal-value" (match sa, sb with
    | .ok a, .ok b => a.val == b.val && a.val == blob2.drop 319 ++ blob2.take 319
    | _, _ => false)
  let (ea, eb) ← both (Flow.Contacts.evict wA 7) (Flow.Contacts.evict wB 7)
  check "contact-evict" (ea matches .ok _ && eb matches .ok _)
  let (k2a, k2b) ← both (Flow.Contacts.key wA 7 (Secret.hide shareA)) (Flow.Contacts.key wB 7 (Secret.hide shareB))
  check "contact-rekey" (k2a matches .ok _ && k2b matches .ok _)
  let wrong := v2 ++ (List.replicate 16 1) ++ blob2.take 319
  let (wa, wb) ← both (Flow.Contacts.load wA 7 wrong) (Flow.Contacts.load wB 7 wrong)
  check "contact-load-refused" (match wa, wb with | .ok a, .ok b => !a.val && !b.val | _, _ => false)
  let stored2 := v2 ++ blob2.drop 319 ++ blob2.take 319
  let (oa, ob) ← both (Flow.Contacts.load wA 7 stored2) (Flow.Contacts.load wB 7 stored2)
  check "contact-reload-accepted" (match oa, ob with | .ok a, .ok b => a.val && b.val | _, _ => false)
  let (aa, ab) ← both (Flow.Contacts.assign wA 7 9) (Flow.Contacts.assign wB 7 9)
  check "contact-assign" (match aa, ab with | .ok a, .ok b => a.val && b.val | _, _ => false)
  -- the state the model holds for the contact is the content (stand-in open of the stored record)
  let t ← (rA.table.get).run
  match t with
  | .ok t =>
    match t.find? 9 with
    | some e =>
      let I := (← st.get).ideal
      check "contact-state-value" (match e.state with
        | some h => (I.bools h.id).map (fun b => ofB8 (bytesOf b)) == some content
        | none => false)
      check "one-counters" ((← (rA.state.get : IO _)).table.ctr.bool == t.ctr.bool)
    | none => IO.println "check contact-table FAIL"
  | .error e => IO.println s!"check contact-table FAIL {e}"
  let tB ← (rB.table.get).run
  check "counters-agree" (match t, tB with | .ok a, .ok b => a.ctr == b.ctr | _, _ => false)
  -- 4. A refused first message (S14's backend on the runner: op 48 holds the envelope, op 50 refuses
  -- it because no receive kernel is loaded; the envelope is freed, nothing is opened).
  let envelope := draw 12 0 300
  let rcvOf (r : Runner.Runner) : ReceiveBackend.Runner :=
    { r.receive with loaded := fun _ => false, programMasks := fun _ => some 0 }
  let ag : ReceiveBackend.Agreements :=
    { agree := fun _ => pure [], kinds := [], reveals := fun _ _ => Every.done _, takes := fun _ => [] }
  let apiOf (r : Runner.Runner) : IO ReceiveBackend.Api := do
    let refs : ReceiveBackend.Refs := { envelope := ← IO.mkRef none, arrival := ← IO.mkRef none }
    let rcv := rcvOf r
    let revealed (_ : Nat) : M (BoolH × Nat) := do
      let h ← ReceiveBackend.runGen rcv (Receive.publicBits (bitsOf (toB8 envelope)))
      return (h, envelope.length)
    return ReceiveBackend.scriptApi rcv (ReceiveBackend.programCurve rcv ag) revealed (throw "no account") 0 refs
  let apiA ← apiOf rA
  let apiB ← apiOf rB
  let (ta, tb) ← both (apiA.take 1 0 300) (apiB.take 1 0 300)
  check "receive-take" (ta matches .ok _ && tb matches .ok _)
  let serverKey := [9] ++ List.replicate 31 0
  let ours := draw 13 0 32
  let (fa, fb) ← both (apiA.openFirst ours 5 serverKey [] [1]) (apiB.openFirst ours 5 serverKey [] [1])
  check "receive-refused" (match fa, fb with
    | .ok (.refused a), .ok (.refused b) => a.val == 0 && b.val == 0
    | _, _ => false)
  IO.println s!"info batches {(← st.get).batches}"
  check "ops-recorded" ((← wA.operations) == [93] && (← wB.operations) == [93])

end RT

def main : IO Unit := RT.main
