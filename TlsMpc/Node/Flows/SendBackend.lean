import TlsMpc.Node.Flows.Send
import TlsMpc.Node.Flows.Account
import TlsMpc.Node.Flows.TlsBackend

/-!
# `Flow.Send.*` from the S13 scripts (ops 41, 42, 61, 62)

REORGANIZATION_PLAN.md stage S13: the send flows of `Flows/SendLegacy.lean` as Lean scripts, with
the legacy functions' results (`Opened .sealedEnvelope (Option (Nat × List Bytes))` for `seal` /
`sealDevices`, `TlsWorker.BufferHandle` for `request` / `requestDevices`) so the callers do not
change; the legacy `Worker` argument becomes the runner context (`TlsBackend.Runner`), as S12's
backends did. Nothing selects these yet: the controller-side runner (op 93) is a parameter, and so
is S11's curve half (`Curve` below; S13_NOTES.md gives the signatures to join).

  * `seal` (op 41): the contact's state (one record), the account's certificate, S11's static
    agreement (`none`: the contact is not ready: refused, the C++'s `{0}`), sender key and one
    ephemeral pair; `Send.sealScript`; on acceptance the contact's state handle is the advanced one
    (the old one was freed by the script); the reply as the legacy one: timestamp (big-endian) and
    the envelope.
  * `sealDevices` (op 61): one ephemeral pair per device; `Send.devicesScript`.
  * `request` / `requestDevices` (ops 42, 62): the request's private part (`Send.requestScript` /
    `requestDevicesScript`), kept under a buffer id with the frame, mask and the kernel's name; the
    name is checked against `find`'s ranges here (the C++ failed at seal time).
  * `sendApplicationBackend`: S12's `scriptApplicationBackend` with `sealApplication` sealing a
    request buffer through `Send.requestCtrScript` then S12's `Tls.tagScript` (`TlsBackend.sealPhases`:
    the shares, this party's half, the tag), and dropping it (a request is sealed once).

Handle ids come from the runner's `allocB` (the session's counters); the contact table is reached
through `TableRef`, which the script runner (`Flows/Runner.lean`, `Runner.table`) points at the table
inside its one state, so `Table.ctr` IS the runner's counters (joined on `scripts-stack`).
-/

namespace TlsMpc.Node.Flows.SendBackend

open TlsMpc.Node.Engine
open TlsMpc.TlsClient (M insist)
open TlsMpc.Node.Flows.Contacts (B8 bitsOf bytesOf)
open TlsMpc.Node.Flows.TlsBackend (Runner toB8 ofB8 seqBytes get set drop)

/-- **S11's half of a send** (`Flows/Curve.lean`, `service_kernels.h` `prepare`, `ephemeral`).
Specification S13 relies on:
  * `ephemeral id`: a fresh ephemeral key pair for a message to contact `id` by the offset
    agreement (P-OFFSET; joint public offset by commit-then-open): the 32-byte public key, opened
    (kind `ephemeralPublic`, its `Reveal` function added by S11), and a FRESH Boolean handle of 255
    private bits, not once, `X25519(e, recipient)` little-endian below p (P-F2W `fieldToWord`); the
    send script consumes (frees) it. No other release than P-OFFSET's kinds.
  * `staticAgreement id`: the contact's static agreement word (`prepare(c)`: `X25519(identity,
    recipient)`), a live handle of 255 private bits kept in the contact's derived caches, or `none`
    when the contact's key is not a point of the curve (`c.ready` false: the send is refused).
  * `senderPublic`: the account's sender key as a 255-bit word handle (live, not once). -/
structure Curve where
  ephemeral : ContactId → M (Opened .ephemeralPublic Bytes × BoolH)
  staticAgreement : ContactId → M (Option BoolH)
  senderPublic : M BoolH

/-- A request's private part between op 42/62 and its record seal. -/
structure Request where
  conv : BoolH
  name : Bytes
  frame : B8
  mask : B8

/-- The session's contact table as the runner holds it (`Flows/Runner.lean`: the table inside the
one script state, so its counters `Table.ctr` are the session's ONE `Counters`, the same ones the
runner's `allocB` draws from). -/
structure TableRef where
  get : M Contacts.Table
  set : Contacts.Table → M Unit

structure Refs (Sc : Type) where
  table : TableRef
  account : IO.Ref Account.State
  requests : IO.Ref (List (Nat × Request))
  tls : TlsBackend.Refs Sc

def certificate (a : Account.State) : M (BoolH × Nat) := do
  let some c := a.certificate | throw "send unavailable"
  return c

/-- The legacy reply's numbers: the big-endian timestamp. -/
def timestampOf (ts : B8) : Nat := Send.beNat ts

/-- **Op 41** (`Flow.Send.seal`). -/
def «seal» {Sc : Type} (r : Runner) (cv : Curve) (s : Refs Sc) (contact : ContactId) (built : Bytes) :
    M (Opened .sealedEnvelope (Option (Nat × List Bytes))) := do
  let t ← s.table.get
  let some e := t.find? contact | throw "send unavailable"
  let some state := e.state | throw "contact state not loaded"
  insist (e.kinds == [0]) "send unavailable"
  let (cert, certLen) ← certificate (← get s.account)
  let some static ← cv.staticAgreement contact | return Reveal.sealedEnvelope none
  let (pk, agr) ← cv.ephemeral contact
  let sender ← cv.senderPublic
  insist (pk.val.length == 32) "ephemeral public key"
  let n ← r.allocB 8
  let res ← r.run (Send.sealScript n ⟨cert, certLen, sender, static, state, toB8 built, toB8 pk.val, agr⟩)
  match res with
  | none => return Reveal.sealedEnvelope none
  | some sd =>
    let t ← s.table.get
    s.table.set (t.put contact { e with state := some sd.state })
    return Reveal.sealedEnvelope (some (timestampOf sd.timestamp, sd.envelopes.map ofB8))

/-- **Op 61** (`Flow.Send.sealDevices`); `address` is our own account's (17 bytes). -/
def sealDevices {Sc : Type} (r : Runner) (cv : Curve) (s : Refs Sc) (contact : ContactId) (address built : Bytes)
    (devices : Nat) : M (Opened .sealedEnvelope (Option (Nat × List Bytes))) := do
  let t ← s.table.get
  let some e := t.find? contact | throw "send unavailable"
  let some state := e.state | throw "send unavailable"
  insist (e.kinds.length == devices && devices > 0) "send unavailable"
  let (cert, certLen) ← certificate (← get s.account)
  let some static ← cv.staticAgreement contact | return Reveal.sealedEnvelope none
  let sender ← cv.senderPublic
  let spans := Contacts.deviceSpans 0 e.kinds
  let mut ds : List Send.DeviceArgs := []
  for (k, sp) in e.kinds.zip spans do
    let (pk, agr) ← cv.ephemeral contact
    insist (pk.val.length == 32) "ephemeral public key"
    ds := ds ++ [⟨k, sp.1.1, toB8 pk.val, agr⟩]
  let n ← r.allocB (10 * devices + 4)
  let res ← r.run (Send.devicesScript n ⟨cert, certLen, sender, static, state, toB8 built, toB8 address, ds⟩)
  match res with
  | none => return Reveal.sealedEnvelope none
  | some sd =>
    let t ← s.table.get
    s.table.set (t.put contact { e with state := some sd.state })
    return Reveal.sealedEnvelope (some (timestampOf sd.timestamp, sd.envelopes.map ofB8))

/-- A fresh buffer id (shared with S12's buffers, so ids never collide). -/
def bufferId {Sc : Type} (s : Refs Sc) : M Nat := do
  let b ← get s.tls.buffers
  set s.tls.buffers { b with next := b.next + 1 }
  return b.next

/-- `find`'s ranges for `signal-request-ctr` (`HybridKernel.find`). -/
def requestOk (cert size : Nat) (offsets : List Nat) : Bool :=
  match offsets with
  | [u, k, d, g] => cert ≤ 1024 && 0 < size && size ≤ 16384 && 8 ≤ u && u + 36 ≤ size && 8 ≤ k &&
      k + 24 ≤ size && 8 ≤ d && d + 3 ≤ size && 8 ≤ g && g + 10 ≤ size
  | _ => false

/-- **Op 42** (`Flow.Send.request`). -/
def request {Sc : Type} (r : Runner) (s : Refs Sc) (contact : ContactId) (offsets : List Nat) (mask frame : Bytes) :
    M TlsWorker.BufferHandle := do
  let t ← s.table.get
  let some e := t.find? contact | throw "request unavailable"
  let some state := e.state | throw "request unavailable"
  let (cert, certLen) ← certificate (← get s.account)
  insist (mask.length == 4 && !frame.isEmpty && requestOk certLen frame.length offsets) "request unavailable"
  let n ← r.allocB 2
  let conv ← r.run (Send.requestScript n cert state)
  let id ← bufferId s
  let rq : Request := ⟨conv, Send.requestNameOf certLen (toB8 frame) offsets, toB8 frame, toB8 mask⟩
  set s.requests ((id, rq) :: (← get s.requests))
  return ⟨id⟩

/-- **Op 62** (`Flow.Send.requestDevices`): the payload's start, the slots' offsets (the contact's
two, then per device two) and the device count. -/
def requestDevices {Sc : Type} (r : Runner) (s : Refs Sc) (contact : ContactId) (payloadAt : Nat) (offsets : List Nat)
    (devices : Nat) (mask frame : Bytes) : M TlsWorker.BufferHandle := do
  let t ← s.table.get
  let some e := t.find? contact | throw "request unavailable"
  let some state := e.state | throw "request unavailable"
  let some name := Send.devicesNameOf (toB8 frame) payloadAt offsets | throw "request unavailable"
  let some pairs := BundleKernel.pairs (offsets.drop 2) | throw "request unavailable"
  insist (mask.length == 4 && !frame.isEmpty && frame.length ≤ 16384 && 6 ≤ payloadAt &&
    e.kinds.length == devices && pairs.length == devices && 1 ≤ devices && devices ≤ 16 &&
    BundleKernel.slotsOk frame.length payloadAt ([(offsets.getD 0 0, 36), (offsets.getD 1 0, 24)] ++
      pairs.flatMap (fun p => [(p.1, 3), (p.2, 10)]))) "request unavailable"
  let ats := (Contacts.deviceSpans 0 e.kinds).map (·.1.1)
  let n ← r.allocB (devices + 1)
  let records ← r.run (Send.requestDevicesScript n state ats)
  let id ← bufferId s
  set s.requests ((id, ⟨records, name, toB8 frame, toB8 mask⟩) :: (← get s.requests))
  return ⟨id⟩

/-- Seal a request buffer, if `id` is one: the request's CTR kernel (`Send.requestCtrScript`), then
S12's shares, half and tag (`TlsBackend.sealPhases`); the buffer is dropped. -/
def sealRequest {Sc : Type} (r : Runner) (s : Refs Sc) (id sequence size padding : Nat) : M (Option Bytes) := do
  let rs ← get s.requests
  match rs.lookup id with
  | none => return none
  | some rq =>
    insist (padding == 0 && size == rq.frame.length) "request padding"
    set s.requests (rs.filter (·.1 != id))
    let some d := (← get s.tls.conn).send | throw "no sending keys"
    let wire ← TlsBackend.sealPhases r s.tls
      (fun n => Send.requestCtrScript n d.traffic rq.conv (seqBytes sequence) rq.frame rq.mask rq.name) 6
    return some wire

/-- **The application records with request buffers** (`TlsApplication.Backend`, as S12's
`scriptApplicationBackend`, which keeps everything else). -/
def sendApplicationBackend {Sc : Type} (r : Runner) (ka : TlsBackend.KeyAgreement Sc) (s : Refs Sc) :
    TlsApplication.Backend TlsWorker.BufferHandle :=
  let base := TlsBackend.scriptApplicationBackend r ka s.tls
  { base with
    sealApplication := fun keys sequence payload size padding => do
      insist (sequence < 2^64) "invalid application seal request"
      match ← sealRequest r s payload.id sequence size padding with
      | some wire => return (Reveal.sealedRecord wire).val
      | none => base.sealApplication keys sequence payload size padding }

end TlsMpc.Node.Flows.SendBackend
