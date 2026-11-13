import TlsMpc.Node.Flows.Tls
import TlsMpc.Node.Flows.Random
import TlsMpc.Node.Reveal
import TlsMpc.TlsApplication

/-!
# `TlsClient.Backend` and `TlsApplication.Backend` from the S12 scripts

REORGANIZATION_PLAN.md stage S12: the TLS client's engine part as Lean scripts, an ALTERNATIVE to
`Flows/TlsLegacy.lean`'s `legacyBackend` / `legacyApplicationBackend` (same types: `Backend Unit`
and `TlsApplication.Backend TlsWorker.BufferHandle`), selectable later. Nothing selects it yet:
the controller-side runner that sends script batches (op 93) does not exist in this branch, so it
is a PARAMETER (`Runner`), as is S11's X25519 agreement (`KeyAgreement`, S12_NOTES.md for the exact
signature to join). Do not use before both are supplied.

WHAT MOVES HERE FROM THE C++ (`tls_kernels.h`, `tls_worker_v3.cpp`):
  * the per-connection secret state (`TlsKernels::Parked`: handshake and traffic key handles, the
    parser state, the GHASH key-power shares of both directions, the scalar between begin and
    derive) is `Tls.Conn` in an `IO.Ref` (to be one entry of `Session/Pool`'s table per
    connection: S12_NOTES.md);
  * the private buffers by public id, the 64-record window and drop-after-seal are `Tls.Buffers`;
  * `GcmShares::ensure` / `half` / `supply`: `ensure` below (Flows/Ghash's scripts, the local
    arithmetic of Local/Ghash on this party's `Secret` shares) and `Local.Ghash.halfOf`;
  * the sequencing of ops 2-7, 12-16, 30, 43.
Every value this file hands to `TlsClient` / `TlsApplication` passes through the same `Reveal.*`
wrapper as the legacy backend's (the reveal list does not change, plan 4.3); every script it runs
declares its kinds (`Tls.*_reveals`, `Ghash.*_reveals`).

NOT HERE (the legacy backend keeps them until S13): sealing a received buffer
(`tls-seal-private-ctr`, used by the echo fixture only) and the request buffers whose sealer is a
service kernel (`PrivateBuffer::sealer`, S13 send flows).
-/

namespace TlsMpc.Node.Flows.TlsBackend

open TlsMpc.Node.Engine
open TlsMpc.TlsClient (M insist liftResult)
open TlsMpc.Node.Flows.Contacts (bitsOf bytesOf B8)
open TlsMpc.Node.Flows.TlsBase (bitsOfW wOfBits bitsOfWs wsOfBits)

abbrev W := BitVec 128

/-! ## The parameters -/

/-- **The controller-side script runner** (S8/S9's interpreter, `Engine.runIO`, sending batches as
op 93; not in this branch). Every party runs the same script with its own store; `run` sends its
batches (the agreement per batch, design note items 4-6 of Engine.lean), feeds the replies to the
continuations, writes `openBoolTo` replies into the named store slots, and returns the script's
result (an `abort` is an error, after which the session is aborted). -/
structure Runner where
  me : Party
  /-- SHA-256 (`Payload.eval`'s `hash`). -/
  hash : Bytes → Bytes
  run : {α : Type} → Script α → M α
  /-- A fresh block of `k` Boolean handle ids (the session's `Counters.allocB`, never reused). -/
  allocB : Nat → M Nat
  /-- A fresh store slot holding this party's private bits (the store write of decision D1). -/
  stashBits : Secret Bits → M Nat
  /-- A fresh store slot holding this party's private bytes (commitment values, nonces). -/
  stashBytes : Secret Bytes → M Nat
  /-- A fresh empty bit slot (an `openBoolTo` destination). -/
  slot : M Nat
  /-- Take a bit slot's content: this party's own secret (what was opened to it alone). -/
  take : Nat → M (Secret Bits)
  /-- `Channels.random`: this party's fresh randomness. -/
  random : Nat → M (Secret Bytes)

/-- **The X25519 agreement, S11's half of the handshake** (`Flows/Curve.lean`: `Curve.split`,
`Curve.agree`). `Sc` is S11's per-connection scalar state. Specification (what S12 relies on):
  * `begin`: draws this party's scalar summand `k_P` (`Channels.random`, clamped as RFC 7748 for
    the sum), opens the joint public key share `u((k_A + k_B)·B)` (kinds `ownPublicPoint`,
    `commitment`, `commitOpening`, `curveChecks`, `maskedDenominator`; P-SPLIT) and returns the
    state and the 32-byte little-endian u-coordinate for the ClientHello;
  * `agree st peer`: with the server's 32-byte key share, its top bit cleared and the value reduced
    mod p (as `tls_kernels.h` `derive`, lines 116-117), computes `X25519(k_A + k_B, peer)` in the
    engines, ABORTS when it is zero (RFC 8446 7.4.2), and returns a fresh Boolean handle of 255
    private bits (marks `never`, not `once`), the little-endian value below p (P-F2W's
    `fieldToWord`), which `deriveScript` consumes and frees; no other release than P-SPLIT's;
  * `erase st`: drops the scalar state (retire, abort; idempotent). -/
structure KeyAgreement (Sc : Type) where
  begin : M (Sc × Bytes)
  agree : Sc → Bytes → M BoolH
  erase : Sc → M Unit

/-! ## Byte conventions -/

def toB8 (b : Bytes) : B8 := b.map fun x => BitVec.ofNat 8 x.toNat
def ofB8 (b : B8) : Bytes := b.map fun x => UInt8.ofNat x.toNat

/-- The 64-bit record sequence, big-endian (`TlsWorker`'s `uint 8`). -/
def seqBytes (n : Nat) : B8 := (List.range 8).map fun i => BitVec.ofNat 8 (n / 256 ^ (7 - i))

/-! ## GHASH key-power shares (`GcmShares::ensure`) -/

/-- The most powers a direction keeps: a full record (16 384 bytes of content, header, lengths). -/
def maxPowers : Nat := Local.Ghash.needed 5 16401

/-- **Shares of H¹ … Hⁿ for a direction, `n ≥ need`** (P-GHASH (a): `Ghash.keyShare_shared`,
`Ghash.round_shared`): the first resharing, then doubling rounds. -/
def ensure (r : Runner) (d : Tls.Direction) (need : Nat) : M Tls.Direction := do
  insist (need ≤ maxPowers) "GHASH power bound"
  let mut d := d
  if d.powers = 0 then
    let mask ← r.random 16
    let maskSlot ← r.stashBits (mask.map fun m => bitsOf (toB8 m))
    let dst ← r.slot
    let n ← r.allocB 3
    r.run (Ghash.keyShareScript n d.traffic maskSlot dst)
    let mine ← if r.me = .a then pure (mask.map fun m => [Local.Ghash.ofBytes (toB8 m)])
      else do pure ((← r.take dst).map fun b => [wOfBits b])
    d := { d with shares := mine, powers := 1 }
  for _ in List.range 16 do
    if d.powers < need then
      let m := d.powers
      let t := min (2 * m) maxPowers
      let c := Local.Ghash.oddCount m t
      if c = 0 then
        -- No odd power in (m, t] (only m = 1, t = 2): the square is local.
        d := { d with shares := Local.Ghash.extendOf d.shares t (Secret.hide []), powers := t }
        continue
      let leftSlot ← r.stashBits ((Local.Ghash.leftsOf d.shares t).map bitsOfWs)
      let rightSlot ← r.stashBits (d.shares.map fun l => bitsOfW (l.getD 0 0))
      let masks ← r.random (16 * c)
      let maskSlot ← r.stashBits (masks.map fun ms => bitsOf (toB8 ms))
      let dst ← r.slot
      let n ← r.allocB 8
      r.run (Ghash.roundScript n c leftSlot rightSlot maskSlot dst)
      let odd ← if r.me = .a then pure (masks.map fun ms => wsOfBits c (bitsOf (toB8 ms)))
        else do pure ((← r.take dst).map (wsOfBits c))
      d := { d with shares := Local.Ghash.extendOf d.shares t odd, powers := t }
  insist (need ≤ d.powers) "GHASH powers"
  return d

/-! ## The state -/

/-- One connection's state and the session's buffers, as the backends hold them. -/
structure Refs (Sc : Type) where
  conn : IO.Ref (Tls.Conn Sc)
  buffers : IO.Ref Tls.Buffers

def get {α : Type} (r : IO.Ref α) : M α := liftM (r.get : IO α)
def set {α : Type} (r : IO.Ref α) (a : α) : M Unit := liftM (r.set a : IO Unit)

def drop (r : Runner) (hs : List BoolH) : M Unit := if hs.isEmpty then pure () else r.run (Tls.dropScript hs)

/-- Erase everything a connection holds (`TlsKernels::abort`): its handles, the scalar, and the
buffers' handles; idempotent. -/
def abortAll {Sc : Type} (r : Runner) (ka : KeyAgreement Sc) (s : Refs Sc) : M Unit := do
  let c ← get s.conn
  if let some sc := c.scalar then ka.erase sc
  let b ← get s.buffers
  set s.conn {}
  set s.buffers {}
  drop r (c.handles ++ (b.table.map (·.2.handles)).flatten)

/-! ## The handshake (ops 1-8) -/

private def handshakeKeys : TlsClient.HandshakeKeys Unit := ⟨(),(),(),(),(),(),()⟩
private def applicationKeys : TlsClient.ApplicationKeys Unit := ⟨(),(),(),(),(),()⟩
private def applicationHandleKeys : TlsClient.ApplicationKeys TlsWorker.BufferHandle := ⟨⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩⟩

def handshakeOf {Sc : Type} (s : Refs Sc) : M Tls.HandshakeHandles := do
  let some h := (← get s.conn).handshake | throw "no handshake keys"
  return h

/-- **The handshake from the scripts**: `TlsClient`'s backend, an alternative to
`Flow.Tls.legacyBackend`. `check` is the local certificate and CertificateVerify validation (the
legacy backend's `pipe.authenticate`). -/
def scriptBackend {Sc : Type} (r : Runner) (ka : KeyAgreement Sc)
    (check : String → List Bytes → Nat → Bytes → Bytes → M Bool) (s : Refs Sc) : TlsClient.Backend Unit where
  begin := do
    let (sc, share) ← ka.begin
    set s.conn { scalar := some sc }
    let nonce ← r.random 32
    let value ← r.random 32
    let ns ← r.stashBytes nonce
    let vs ← r.stashBytes value
    let random ← r.run (Random.joint r.hash r.me ns vs)
    insist (share.length == 32 && random.length == 32) "invalid key share or random length"
    let opened := Reveal.handshakeShare share random
    return ((), opened.val.1, opened.val.2)
  derive _ peer hash := do
    insist (peer.length == 32 && hash.length == 32) "invalid public agreement inputs"
    let c ← get s.conn
    let some sc := c.scalar | throw "derive before begin"
    let agreement ← ka.agree sc peer
    let n ← r.allocB 6
    let h ← r.run (Tls.deriveScript n agreement (toB8 hash))
    set s.conn { c with handshake := some h }
    return handshakeKeys
  openHandshake _ sequence wire := do
    insist (sequence < 2^64 && 22 ≤ wire.length && wire.length ≤ 16645) "invalid handshake record"
    let h ← handshakeOf s
    let n ← r.allocB 3
    let output := ofB8 (← r.run (Tls.openHandshakeScript n h.server (seqBytes sequence) (toB8 wire)))
    insist (output.length ≥ 4 && output[0]?.getD 0 == 255) "handshake record rejected"
    let kind := (output[1]?.getD 0).toNat
    let size := 256 * (output[2]?.getD 0).toNat + (output[3]?.getD 0).toNat
    insist ((kind == 21 || kind == 22) && size ≤ output.length - 4) "invalid public handshake output"
    return (Reveal.handshakeRecord kind ((output.drop 4).take size)).val
  authenticate hostname chain scheme hash signature := do
    let valid ← check hostname chain scheme hash signature
    -- The whole request and the local decision, agreed through the batch skeleton (op 4's rule):
    -- a disagreement aborts both parties instead of accepting the leader's decision.
    let digest := toB8 (TlsWire.hash (TlsWorker.authRequest hostname chain scheme hash signature valid))
    let n ← r.allocB 1
    r.run (Tls.agreeScript n digest valid)
    return valid
  verifyFinished _ hash message := do
    insist (hash.length == 32 && message.length == 36) "invalid Finished inputs"
    let h ← handshakeOf s
    let n ← r.allocB 3
    let ok ← r.run (Tls.verifyScript n h.server (toB8 hash) (toB8 message))
    return (Reveal.finishedAccepted ok).val
  finish _ serverHash clientHash certificate := do
    insist (serverHash.length == 32 && clientHash.length == 32 &&
      (certificate.isEmpty || certificate == TlsClient.emptyCertificate)) "invalid client Finished context"
    let c ← get s.conn
    let some h := c.handshake | throw "no handshake keys"
    let n ← r.allocB 7
    let (wire, clientApp, serverApp) ←
      r.run (Tls.finishScript n h.main h.client (toB8 serverHash) (toB8 clientHash) (toB8 certificate))
    set s.conn { c with send := some { traffic := clientApp }, receive := some { traffic := serverApp } }
    let wire := ofB8 wire
    let (records, pending) ← liftResult (TlsWire.records 2 wire)
    insist (records.length == 1 && pending.isEmpty &&
      records.head!.kind == 23 && records.head!.version == 0x0303) "invalid encrypted Finished record"
    return (applicationKeys, (Reveal.clientFinished wire).val)
  retire _ _ := do
    let c ← get s.conn
    if let some sc := c.scalar then ka.erase sc
    set s.conn { c with scalar := none, handshake := none }
    drop r ((c.handshake.map fun h => [h.client, h.server, h.main]).getD [])
  abort := abortAll r ka s

/-! ## The application records (ops 12-16, 30, 43) -/

def sendOf {Sc : Type} (s : Refs Sc) : M Tls.Direction := do
  let some d := (← get s.conn).send | throw "no sending keys"
  return d

/-- **Seal a record, the three phases** (`tagged`): the CTR kernel's header ‖ ciphertext (opened),
the shares, this party's half, the tag. -/
def sealPhases {Sc : Type} (r : Runner) (s : Refs Sc) (ctr : Nat → Script (B8 × BoolH)) (ctrIds : Nat) : M Bytes := do
  let n ← r.allocB ctrIds
  let (hc, pad) ← r.run (ctr n)
  let d ← ensure r (← sendOf s) (Local.Ghash.needed 5 (hc.length - 5))
  set s.conn { (← get s.conn) with send := some d }
  let halfSlot ← r.stashBits ((Local.Ghash.halfOf d.shares (hc.take 5) (hc.drop 5)).map bitsOfW)
  let m ← r.allocB 4
  let tag ← r.run (Tls.tagScript m pad halfSlot)
  return ofB8 (hc ++ tag)

/-- **The application records from the scripts**: `TlsApplication`'s backend, an alternative to
`Flow.Tls.legacyApplicationBackend`. -/
def scriptApplicationBackend {Sc : Type} (r : Runner) (ka : KeyAgreement Sc) (s : Refs Sc) :
    TlsApplication.Backend TlsWorker.BufferHandle where
  sealApplication _ sequence payload size padding := do
    insist (sequence < 2^64 && 0 < payload.id && size + padding ≤ 16384) "invalid application seal request"
    let b ← get s.buffers
    let some buf := b.find? payload.id | throw "application seal request"
    let d ← sendOf s
    let wire ← match buf with
      | .publicBytes content size' =>
        insist (size' == size) "application seal size"
        if padding == 0 then
          sealPhases r s (fun n => Tls.sealClassScript n d.traffic content (seqBytes sequence) size) 6
        else
          sealPhases r s (fun n => Tls.sealCtrScript n d.traffic content (seqBytes sequence) 23 size padding) 5
      | .received .. => throw "sealing a received buffer is not a script flow (legacy backend only)"
    -- Drop after seal (`tls_worker_v3.cpp:336-338`): a buffer is sealed into exactly one record.
    let (hs, b') := (← get s.buffers).sealed payload.id
    set s.buffers b'
    drop r hs
    return (Reveal.sealedRecord wire).val
  sealControl _ sequence kind content := do
    insist (sequence < 2^64 &&
      ((kind == 22 && (content == [24,0,0,1,0] || content == [24,0,0,1,1])) ||
        (kind == 21 && content == [1,0]))) "invalid TLS control"
    let d ← sendOf s
    let n ← r.allocB 1
    let body ← r.run (Tls.publicScript n (toB8 content))
    let wire ← sealPhases r s
      (fun m => Tls.sealCtrScript m d.traffic body (seqBytes sequence) kind content.length 0) 5
    drop r [body]
    return (Reveal.sealedRecord wire).val
  openRecord _ sequence wire := do
    insist (sequence < 2^64 && 22 ≤ wire.length && wire.length ≤ 16406 &&
      wire.length == 5 + 256 * (wire[3]?.getD 0).toNat + (wire[4]?.getD 0).toNat) "invalid application open request"
    let c ← get s.conn
    let some d := c.receive | throw "no receiving keys"
    let parser ← match c.parser with
      | some p => pure p
      | none => do let n ← r.allocB 2; r.run (Tls.parserScript n)
    let hdr := toB8 (wire.take 5)
    let ct := toB8 ((wire.drop 5).take (wire.length - 21))
    let d ← ensure r d (Local.Ghash.needed 5 ct.length)
    let halfSlot ← r.stashBits ((Local.Ghash.halfOf d.shares hdr ct).map bitsOfW)
    let cap := Tls.capacity wire.length
    let padded := toB8 wire ++ List.replicate (cap - wire.length) 0
    let n ← r.allocB 17
    let o ← r.run (Tls.openScript n parser d.traffic (seqBytes sequence) (toB8 (wire.drop (wire.length - 16)))
      padded (toB8 ((wire.drop 3).take 2)) cap halfSlot)
    set s.conn { c with receive := some d, parser := some o.parser }
    drop r [parser]
    let event := ofB8 o.event
    insist (event.length == 2) "application event"
    let e := (event[0]?.getD 255).toNat
    let q := (event[1]?.getD 255).toNat
    if e == 1 then
      insist (q == 0) "invalid payload event"
      -- The 64-record window (`tls_worker_v3.cpp:321-329`): the oldest beyond 64 are dropped.
      let (id, hs, b') := (← get s.buffers).receive (.received o.length o.content (cap - 21) none)
      set s.buffers b'
      drop r hs
      return (Reveal.recordEvent (.application ⟨id⟩)).val
    drop r [o.length, o.content]
    match e with
    | 0 => insist (q == 0) "invalid rejection flag"; return (Reveal.recordEvent .fatal).val
    | 2 => insist (q == 0) "invalid ignored-control flag"; return (Reveal.recordEvent .skippedControl).val
    | 3 => insist (q ≤ 1) "invalid KeyUpdate request flag"; return (Reveal.recordEvent (.keyUpdate (q == 1))).val
    | 4 => insist (q == 0) "invalid close flag"; return (Reveal.recordEvent .closeNotify).val
    | _ => throw "invalid application event"
  rotateSend _ := do
    let c ← get s.conn
    let some d := c.send | throw "no sending keys"
    let n ← r.allocB 1
    let t ← r.run (Tls.updateScript n d.traffic)
    -- The key-power shares belong to the old key.
    set s.conn { c with send := some { traffic := t } }
    return applicationHandleKeys
  rotateReceive _ := do
    let c ← get s.conn
    let some d := c.receive | throw "no receiving keys"
    let n ← r.allocB 1
    let t ← r.run (Tls.updateScript n d.traffic)
    set s.conn { c with receive := some { traffic := t } }
    return applicationHandleKeys
  abort := abortAll r ka s

/-! ## Public buffers and the server-byte reveal (ops 30, 43) -/

/-- **Public bytes into the engines, to be sealed and sent** (op 30). -/
def publicBuffer {Sc : Type} (r : Runner) (s : Refs Sc) (bytes : Bytes) : M TlsWorker.BufferHandle := do
  insist (!bytes.isEmpty && bytes.length ≤ 16384) "public buffer size"
  let n ← r.allocB 1
  let h ← r.run (Tls.publicScript n (toB8 bytes))
  let (id, b') := (← get s.buffers).add (.publicBytes h bytes.length)
  set s.buffers b'
  return ⟨id⟩

/-- The masked bytes of a received buffer and its revealed length (computed once per buffer). -/
def revealed {Sc : Type} (r : Runner) (s : Refs Sc) (handle : Nat) : M (BoolH × Nat) := do
  let b ← get s.buffers
  match b.find? handle with
  | some (.received length content cap (some rv)) => let _ := (length, content, cap); return rv
  | some (.received length content cap none) =>
    let n ← r.allocB 4
    let (len, bytes) ← r.run (Tls.revealScript n length content cap)
    insist (len ≤ cap) "revealed length"
    set s.buffers { b with table := b.table.map fun e =>
      if e.1 == handle then (e.1, .received length content cap (some (bytes, len))) else e }
    return (bytes, len)
  | _ => throw "reveal handle"

/-- **The length of an authenticated record** (op 43 past any record): no byte. -/
def recordLength {Sc : Type} (r : Runner) (s : Refs Sc) (handle : Nat) : M (Opened .serverBytes (Nat × Bytes)) := do
  let (_, len) ← revealed r s handle
  pure (Reveal.serverBytes len [])

/-- **Reveal `count` bytes of an authenticated record from `offset`** (op 43): the record's length
and the bytes (none past the length; `Tls.range_value`: they are the server's plaintext bytes).

PRECONDITION (T1, not checked here): the caller asks only for positions the receive policy may
reveal (`PublicReceive.mayReveal` within `PublicReceive.budget`, `Policy/Receive.lean`): T1's
invariant, which `ReceiveLoop.t1_all` proves for every byte stream (main checkout, the T1 upgrade):
no revealed position lies in `hidden` (request and response bodies, envelope payloads). This
function does not know the stream; it is the reveal list's `serverBytes` opening, bounded by T1
through its caller. -/
def revealRange {Sc : Type} (r : Runner) (s : Refs Sc) (handle offset count : Nat) :
    M (Opened .serverBytes (Nat × Bytes)) := do
  insist (0 < count) "reveal count"
  let (bytes, len) ← revealed r s handle
  if offset < len then
    let stop := min len (offset + count)
    let n ← r.allocB 1
    let out ← r.run (Tls.rangeScript n bytes offset stop)
    pure (Reveal.serverBytes len (ofB8 out))
  else pure (Reveal.serverBytes len [])

end TlsMpc.Node.Flows.TlsBackend
