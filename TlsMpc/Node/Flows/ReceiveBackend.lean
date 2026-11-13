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

/-- S11's agreements with their kinds (`Receive.Curve.agree`; S14_NOTES.md). -/
structure Agreements where
  agree : List Job → Gen (List BoolH)
  kinds : List TlsMpc.Node.RevealKind
  reveals : ∀ jobs st, Reveals kinds (agree jobs st)

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

/-- The three programs' masks for one message: fresh contributions in store slots. -/
def programMasks (r : Runner) : M ProgramMasks := do
  let one (name : Bytes) : M (Nat × Nat) := do
    let some k := r.programMasks name | throw "receive program shape"
    if k = 0 then return (0, 0)
    return (k, ← r.stashElems (← elems r k))
  let (c, cs) ← one xeddsaCheckName
  let (rc, rs) ← one xeddsaRecoverName
  let (t, ts) ← one torsionName
  return { check := c, checkSlot := cs, recover := rc, recoverSlot := rs, torsion := t, torsionSlot := ts }

/-- The non-hinted curve pieces for one message: S11's agreements and the three programs. -/
def programCurve (r : Runner) (ag : Agreements) : M Curve := do
  return Curve.withPrograms ag.agree ag.kinds ag.reveals (← programMasks r)

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

/-- **The receive functions from the scripts.** `curve`: the curve pieces for one message
(`programCurve r ag`, or S11's hinted ones); `revealed`: a received buffer's revealed bytes and
length (`TlsBackend.revealed`); `account`: our sender certificate's handle and length (the account
state); `jump`: `SIGNAL_RECEIVE_JUMP`. -/
def scriptApi (r : Runner) (curve : M Curve) (revealed : Nat → M (BoolH × Nat)) (account : M (BoolH × Nat))
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
    let cv ← curve
    let fi : FirstIn :=
      ⟨toB8 identityPublic, toB8 (TlsMpc.TlsWire.uint 8 now), sx, sy, toB8 serverCertificate, toB8 signerId⟩
    match ← runGen r (Receive.openFirst cv r.loaded fi env size) with
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
    let cv ← curve
    let sp : SessionPublic := { address := toB8 address, requestId := toB8 (TlsMpc.TlsWire.uint 8 (2 ^ 63)), jump }
    let ss : SessionSecrets := { certificate, cert, signedSlot, oneTimeSlot, kemSlot, ratchetSlot }
    match ← runGen r (Receive.session cv r.loaded a sp ss) with
    | none => return .refused (Reveal.sessionStatus 0)
    | some (text, record) =>
      let st ← get r.state
      let entry : Contacts.Entry := { state := some record, size := contactBytes, kinds := [0] }
      set r.state { st with table := st.table.put contact entry }
      return .text (Reveal.receivedText ((String.fromUTF8? ⟨(ofB8 text).toArray⟩).getD ""))

end TlsMpc.Node.Flows.ReceiveBackend
