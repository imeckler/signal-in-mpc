import TlsMpc.Node.Flows.Receive
import TlsMpc.Node.Flows.ReceiveLegacy
import TlsMpc.Signal.XEdDsaField

/-!
# `Receive.take/drop/openFirst/session` from the S14 scripts, with the legacy signatures

REORGANIZATION_PLAN.md stage S14: the IO glue around `Flows/Receive.lean`'s scripts, an
ALTERNATIVE to `Flows/ReceiveLegacy.lean` (worker ops 48-51) with the same function types once the
context is supplied (`Api`; `legacy_api_types` checks that the legacy functions have exactly these
types). Nothing selects it yet: the controller-side runner sending script batches (op 93) is not
in this branch, so it is a PARAMETER (`Runner`), as are S11's agreements (`Receive.Curve`) and
S12's revealed buffers (`TlsBackend.revealed`). Do not use before all are supplied.

WHAT MOVES HERE FROM THE C++ (`service_kernels.h`):
  * the held envelope (`envelope`) and arrival (`Arrival`, `arrival.held`) as `Refs`;
  * `server(...)`: the server key as an Edwards point, computed LOCALLY by each node from the public
    key (owner decision: `xeddsa-recover`'s outputs stay secret; its public-input use is the Lean
    definition `XEdDsaField.run X25519.concrete true` evaluated in the clear, as the C++'s hinted
    path's `evaluate_clear` does), refusing a key out of range or off the curve (`need`);
  * the program masks (fresh field contributions from `Channels.random`, rule 5);
  * the new contact's record entered in the contact table under its id (`conversations[id]`).
The KEM decapsulation stays OUTSIDE (the caller's `Channels.kemDecapsulate`, a local tool with the
key on stdin): the session takes its result as a `Secret`, as the legacy `session` does.
-/

namespace TlsMpc.Node.Flows.ReceiveBackend

open TlsMpc.Node.Engine
open TlsMpc.TlsClient (M insist)
open TlsMpc.Node.Flows.Contacts (bitsOf bytesOf B8)
open TlsMpc.Node.Flows.Receive
open TlsMpc.FieldDag (F)

/-! ## The parameters -/

/-- **The controller-side script runner** (S8/S9's interpreter, op 93 batches; not in this branch).
Both parties run the same script with their own stores; `run` sends its batches (the agreement per
batch), feeds the replies to the continuations and returns the result (an `abort` is an error,
after which the session is aborted). `state` is the session's public script state (the contact
table with the handle counters, the mask pool); the stash functions put this party's private data
in fresh store slots (decision D1). -/
structure Runner where
  me : Party
  run : {α : Type} → Script α → M α
  state : IO.Ref St
  stashBits : Secret Bits → M Nat
  stashBytes : Secret Bytes → M Nat
  stashElems : Secret (List F) → M Nat
  /-- `Channels.random`: this party's fresh randomness. -/
  random : Nat → M (Secret Bytes)
  /-- The kernels the worker loaded (the manifest's names, fixed at session start). -/
  loaded : Bytes → Bool
  /-- The V3 programs the worker loaded: their mask counts (`ProgSig.masks`). -/
  programMasks : Bytes → Option Nat

/-- S11's agreements with their kinds (`Receive.Curve.agree`; S14_NOTES.md), and (J1) the element
counts of the slots one call on `n` jobs takes from the supply (`Join.receiveAgree`: `[n]`, its
quotient masks). -/
structure Agreements where
  agree : List Job → Gen (List BoolH)
  kinds : List TlsMpc.Node.RevealKind
  reveals : ∀ jobs st, Reveals kinds (agree jobs st)
  takes : Nat → List Nat

/-- The receive state between the operations (the C++ `envelope`, `arrival`). -/
structure Refs where
  envelope : IO.Ref (Option (BoolH × Nat))
  arrival : IO.Ref (Option Arrival)

def get {α : Type} (r : IO.Ref α) : M α := liftM (r.get : IO α)
def set {α : Type} (r : IO.Ref α) (a : α) : M Unit := liftM (r.set a : IO Unit)

def toB8 (b : Bytes) : B8 := b.map fun x => BitVec.ofNat 8 x.toNat
def ofB8 (b : B8) : Bytes := b.map fun x => UInt8.ofNat x.toNat

/-- Run a state-threaded script: the session's state in, the state it leaves out. -/
def runGen {α : Type} (r : Runner) (g : Gen α) : M α := do
  let st ← get r.state
  let (a, st') ← r.run (g st)
  set r.state st'
  return a

/-! ## Local pieces -/

/-- `k` fresh field elements of this party (64 random bytes each, reduced mod p: statistical
distance below 2⁻²⁵⁰ from uniform). -/
def elems (r : Runner) (k : Nat) : M (Secret (List F)) := do
  let bytes ← r.random (64 * k)
  return bytes.map fun b => (List.range k).map fun i =>
    TlsMpc.FieldDag.ofNat (Engine.fromLE ((b.drop (64 * i)).take 64))

/-- **The server key as an Edwards point, locally** (`service_kernels.h` `server`): the key's
u-coordinate (top bit cleared) must be below p, and `xeddsa-recover`'s Lean definition evaluated
in the clear must say "a curve point" (output 0 is 1); then its x and y. -/
def serverPoint (key : Bytes) : Option (Nat × Nat) :=
  let u := Engine.fromLE (key.take 31 ++ [(key.getD 31 0) &&& 127])
  if u < TlsMpc.FieldDag.modulus then
    let pt := TlsMpc.Signal.XEdDsaField.run TlsMpc.X25519.concrete true (fun _ => TlsMpc.FieldDag.ofNat u)
    if pt.getD 0 (TlsMpc.FieldDag.ofNat 0) = TlsMpc.FieldDag.ofNat 1 then
      some ((pt.getD 1 (TlsMpc.FieldDag.ofNat 0)).val, (pt.getD 2 (TlsMpc.FieldDag.ofNat 0)).val)
    else none
  else none

/-- The three programs' mask counts (the pinned programs', fixed at session start). -/
def programMasks (r : Runner) : M ProgramMasks := do
  let one (name : Bytes) : M Nat := do
    let some k := r.programMasks name | throw "receive program shape"
    return k
  return { check := ← one xeddsaCheckName, recover := ← one xeddsaRecoverName, torsion := ← one torsionName }

/-- Which receive operation a supply is for: op 50, or op 51 (with or without a one-time prekey). -/
inductive Op where
  | first
  | session (oneTime : Bool)

/-- **J1: the element counts of the slots an operation takes from the supply, in its order**:
op 50 its two agreements (one job each) then `xeddsa-check`; op 51 `xeddsa-recover`,
`receive-torsion`, then its agreements (6 jobs, 7 with a one-time prekey). A program without masks
takes nothing (`Receive.maskSlot`). -/
def counts (ag : Agreements) (pm : ProgramMasks) : Op → List Nat
  | .first => ag.takes 1 ++ ag.takes 1 ++ (if pm.check = 0 then [] else [pm.check])
  | .session oneTime => (if pm.recover = 0 then [] else [pm.recover]) ++
      (if pm.torsion = 0 then [] else [pm.torsion]) ++ ag.takes (if oneTime then 7 else 6)

/-- Fresh slots for `cs`: per count a new store slot holding that many fresh field elements of this
party (rule 5); every slot is new (`stashElems`), so no two entries share one. -/
def supplyOf (r : Runner) : List Nat → M (List (Nat × Nat))
  | [] => pure []
  | c :: cs => do
    let s ← r.stashElems (← elems r c)
    let rest ← supplyOf r cs
    pure ((s, c) :: rest)

/-- The non-hinted curve pieces for one operation: S11's agreements and the three programs, and the
supply of fresh slots the operation takes (J1: built anew for every operation). -/
def programCurve (r : Runner) (ag : Agreements) (op : Op) : M (Curve × List (Nat × Nat)) := do
  let pm ← programMasks r
  return (Curve.withPrograms ag.agree ag.kinds ag.reveals pm, ← supplyOf r (counts ag pm op))

/-- Run an operation's script with its own supply of fresh slots (J1): the supply is set before the
script and whatever it did not take is dropped after it (never handed to another operation). -/
def runWith {α : Type} (r : Runner) (supply : List (Nat × Nat)) (g : Gen α) : M α := do
  let st ← get r.state
  set r.state { st with slots := supply }
  let a ← runGen r g
  set r.state { (← get r.state) with slots := [] }
  return a

/-! ## The flow API with the legacy signatures -/

/-- The four receive functions as the controller calls them (`Flow.Receive.*` with the worker
supplied). -/
structure Api where
  take : Nat → Nat → Nat → M Unit
  drop : M Unit
  openFirst : Bytes → Nat → Bytes → Bytes → Bytes → M Flow.FirstMessage
  session : ContactId → Bytes → Secret Bytes → Secret Bytes → Secret Bytes → M Flow.Received

/-- **The legacy functions have exactly these types**: switching the controller from
`Flow.Receive.*` (ops 48-51) to `scriptApi` changes no call site's arguments or results. -/
def legacyApi (w : Flow.Worker) : Api where
  take := Flow.Receive.take w
  drop := Flow.Receive.drop w
  openFirst := Flow.Receive.openFirst w
  session := Flow.Receive.session w

/-- **The receive functions from the scripts.** `curve`: the curve pieces for one operation and the
supply of fresh slots it takes (`programCurve r ag`, or S11's hinted ones; J1: a new supply per
operation); `revealed`: a received buffer's revealed bytes and length (`TlsBackend.revealed`);
`account`: our sender certificate's handle and length (the account state); `jump`:
`SIGNAL_RECEIVE_JUMP`. -/
def scriptApi (r : Runner) (curve : Op → M (Curve × List (Nat × Nat))) (revealed : Nat → M (BoolH × Nat))
    (account : M (BoolH × Nat))
    (jump : Nat) (s : Refs) : Api where
  take handle offset count := do
    let (bytes, len) ← revealed handle
    insist (0 < count && offset + count ≤ len) "take range"
    let env ← get s.envelope
    insist ((env.map (·.2)).getD 0 + count ≤ maxEnvelope) "envelope take"
    let held ← runGen r (takeScript env bytes offset count)
    set s.envelope (some held)
  drop := do
    let env ← get s.envelope
    let a ← get s.arrival
    set s.envelope none
    set s.arrival none
    runGen r (dropScript env a)
  openFirst identityPublic now serverKey serverCertificate signerId := do
    insist (identityPublic.length == 32 && serverKey.length == 32) "envelope open"
    let some (env, size) ← get s.envelope | throw "envelope open"
    insist (← get s.arrival).isNone "envelope open"
    set s.envelope none
    let some (sx, sy) := serverPoint serverKey | throw "server key is not a curve point"
    let (cv, supply) ← curve .first
    let fi : FirstIn :=
      ⟨toB8 identityPublic, toB8 (TlsMpc.TlsWire.uint 8 now), sx, sy, toB8 serverCertificate, toB8 signerId⟩
    match ← runWith r supply (Receive.openFirst cv r.loaded fi env size) with
    | none => return .refused (Reveal.sessionStatus 0)
    | some ((one, b), a) =>
      set s.arrival (some a)
      insist (b.length == 12 + 1568) "invalid opened prekey message"
      let o := ofB8 b
      return .opened (Reveal.prekeyIds
        { usesOneTime := one, oneTime := TlsMpc.TlsWire.number (o.take 4),
          signed := TlsMpc.TlsWire.number ((o.drop 4).take 4), kyber := TlsMpc.TlsWire.number ((o.drop 8).take 4),
          kyberCiphertext := o.drop 12 })
  session contact address signed oneTime secret := do
    let some a ← get s.arrival | throw "envelope session"
    set s.arrival none
    let st ← get r.state
    insist (address.length == 17 && signed.length == 32 && oneTime.length == 32 && secret.length == 32 &&
      (st.table.find? contact).isNone) "envelope session"
    let (certificate, cert) ← account
    let signedSlot ← r.stashBytes signed
    let oneTimeSlot ← r.stashBytes oneTime
    let kemSlot ← r.stashBits (secret.map fun b => bitsOf (toB8 b))
    let ratchetSlot ← r.stashBytes (← r.random 32)
    let (cv, supply) ← curve (.session a.oneTime)
    let sp : SessionPublic := { address := toB8 address, requestId := toB8 (TlsMpc.TlsWire.uint 8 (2 ^ 63)), jump }
    let ss : SessionSecrets := { certificate, cert, signedSlot, oneTimeSlot, kemSlot, ratchetSlot }
    match ← runWith r supply (Receive.session cv r.loaded a sp ss) with
    | none => return .refused (Reveal.sessionStatus 0)
    | some (text, record) =>
      let st ← get r.state
      let entry : Contacts.Entry := { state := some record, size := contactBytes, kinds := [0] }
      set r.state { st with table := st.table.put contact entry }
      return .text (Reveal.receivedText ((String.fromUTF8? ⟨(ofB8 text).toArray⟩).getD ""))

end TlsMpc.Node.Flows.ReceiveBackend
