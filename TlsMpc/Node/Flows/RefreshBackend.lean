import TlsMpc.Node.Flows.Runner
import TlsMpc.Node.Flows.RefreshLegacy

/-!
# `Flow.Refresh.*` from the S15 scripts (ops 56-60, 64, 65), with the legacy signatures

REORGANIZATION_PLAN.md stage S15, the IO glue S15 lacked (STACK_NOTES.md F46): an ALTERNATIVE to
`Flows/RefreshLegacy.lean` with the same function types (`Api`; `legacyApi` checks that the legacy
functions have exactly these types), like `SendBackend` / `ReceiveBackend`. It runs S15's steps
(`Refresh.opFetch` … `opCommit`, `opEstablish` with the joined curve `Join.refreshOps`) through the
runner (`Flows/Runner.lean`), on the runner's contact table (one `Counters`).

  * `fetch` (op 56): checked as `opFetch` does, kept as a pending request under a buffer id (shared
    with S12's buffers); `sealFetch` seals it when the record layer seals that buffer
    (`Refresh.fetchScript` with S12's traffic key and sequence, then S12's tag phases), as
    `SendBackend.sealRequest` does for op 42.
  * `take` / `drop` / `shape` / `scratchSeal` / `scratchCommit`: `opTake` (the received buffer's
    content handle from S12's buffers), `opDrop`, `opShape`, `opScratchSeal`, `opCommit`.
  * `establish` (op 60): one step; `curveFor` builds the step's `Join.RefreshCurve`: EACH CALL ITS
    OWN word masks and bit pairs taken from the session pool (`takePool`: each mask handed out once,
    P-CUT (h); the J1 sibling fixed in `Join.RefreshCurve`) and its own supply of NEW store slots of
    fresh field contributions (`Runner.supply`, J1), only for the calls the step makes (step 0:
    `lift` on the first device or a new identity, `check`; step 1: `agree`). The agreements' scalars:
    the account's identity scalar's swap bits as field handles (J8, `Sources.identitySwaps`, no
    coins), and as coins this party's
    swap-bit shares of two fresh random scalars (`swapCoins`, X25519SwapBits.swapBit_shares: the
    shares' XOR is the swap bit of the XORed scalar, party A with the top bit). Step 2's entropy:
    32 fresh random bytes of this party.
The reply bytes pass through the same `Reveal.*` wrappers as the legacy ones.

UNVERIFIED IO glue, like the other backends. No I/O primitive (`IO.Ref` only); no emitter imports
this module.
-/

namespace TlsMpc.Node.Flows.RefreshBackend

open TlsMpc.Node.Engine
open TlsMpc.TlsClient (M insist)
open TlsMpc.Node.Flows.Contacts (B8 bitsOf bytesOf)
open TlsMpc.Node.Flows.Runner (Runner)
open TlsMpc.Node.Flows.TlsBackend (toB8 ofB8 seqBytes)
open TlsMpc.FieldDag (F)

/-- A prekey fetch's request between op 56 and its record seal. -/
structure Fetch where
  contact : Nat
  payloadAt : Nat
  uuidAt : Nat
  keyAt : Nat
  frame : B8
  mask : B8

/-- The refresh's state between the operations (the C++ `bundle`, `scratch`). -/
structure Refs where
  state : IO.Ref Refresh.RState
  fetches : IO.Ref (List (Nat × Fetch))

def get {α : Type} (r : IO.Ref α) : M α := (r.get : IO α)
def set {α : Type} (r : IO.Ref α) (a : α) : M Unit := (r.set a : IO Unit)

/-- What the refresh reads from the rest of the session. -/
structure Sources (Sc : Type) where
  /-- The runner's contact table (its counters: the session's). -/
  table : SendBackend.TableRef
  /-- The account's handles the establishment reads (`Refresh.Account`). -/
  account : M Refresh.Account
  /-- J8: the account's identity scalar's 252 swap bits as field handles (`Account.State.identity`,
  op 55's); no coins slot for the identity scalar. -/
  identitySwaps : M (List FieldH)
  /-- S12's connection and buffers (the received records, the send direction's key). -/
  tls : TlsBackend.Refs Sc

/-- The legacy reply's shape for the four functions that take arguments. -/
structure Api where
  fetch : ContactId → Nat → List Nat → Bytes → Bytes → M TlsWorker.BufferHandle
  take : Nat → Nat → Nat → M Unit
  drop : M Unit
  shape : M (Option (Opened .bundleShape (List Bool)))
  establish : ContactId → Nat → Nat → Nat → Nat → Nat → Bool → TlsMpc.Signal.BundleResponse.Widths →
    M (Opened .deviceStatus Bytes)
  scratchSeal : ContactId → Bytes → M (Opened .sealedBlob Bytes)
  scratchCommit : ContactId → M Unit

/-- **The legacy functions have exactly these types.** -/
def legacyApi (w : Flow.Worker) : Api where
  fetch := Flow.Refresh.fetch w
  take := Flow.Refresh.take w
  drop := Flow.Refresh.drop w
  shape := Flow.Refresh.shape w
  establish := Flow.Refresh.establish w
  scratchSeal := Flow.Refresh.scratchSeal w
  scratchCommit := Flow.Refresh.scratchCommit w

/-! ## Local pieces -/

/-- **This party's swap-bit shares of a scalar share** (coins for `Convert.sharedBits`): ladder
steps 2 … 253 of `X25519SwapBits` on the share's 256 bits, the top step's negation (the clamped
scalar's bit 254) on party A's side only, so the two parties' coins XOR to the swap bits of the
XOR of their shares (`X25519SwapBits.swapBit_shares`). -/
abbrev swapCoins (me : Party) (share : Bytes) : List F := ReceiveBackend.swapCoins me share

/-- Take `words` word masks and `bits` bit pairs from the session's pool (each handed out once). -/
def takePool (r : Runner) (words bits : Nat) : M Conv.MaskPool := do
  let st ← Runner.get r.state
  insist (words ≤ st.pool.words.length && bits ≤ st.pool.bits.length) "mask pool"
  Runner.set r.state { st with pool := { words := st.pool.words.drop words, bits := st.pool.bits.drop bits } }
  return { words := st.pool.words.take words, bits := st.pool.bits.take bits }

/-- The program mask counts (the pinned programs', fixed at session start). -/
def counts (r : Runner) (name : Bytes) : M Nat := do
  let some k := r.programMasks name | throw "refresh program shape"
  return k

/-- The element counts of a call's supply (J1): one slot per program step with masks. -/
def nonzero (cs : List Nat) : List Nat := cs.filter (· != 0)

/-- **One establishment step's curve calls** (`Join.RefreshCurve`), prepared for the calls this step
makes only: step 0 `lift` (device 0, or no lifted key yet) and `check`; step 1 `agree` (7 jobs with a
one-time prekey). Every call its own pool and its own supply of new slots. -/
def curveFor {Sc : Type} (r : Runner) (src : Sources Sc) (st : Refresh.RState) (index step : Nat) :
    M Join.RefreshCurve := do
  let recover ← counts r Receive.xeddsaRecoverName
  let check ← counts r Receive.xeddsaCheckName
  let lifting := step = 0 && (index = 0 || st.lifted.isNone)
  let liftPool ← if lifting then takePool r Join.liftWords 0 else pure {}
  let liftSlots ← if lifting then r.supply (nonzero [recover]) else pure []
  let checkPool ← if step = 0 then takePool r Join.checkWords Join.checkBits else pure {}
  let checkSlots ← if step = 0 then r.supply (nonzero [check, check]) else pure []
  let oneTime := (st.progress.map (·.oneTime)).getD false
  let agreePool ← if step = 1 then takePool r Join.agreeWords 0 else pure {}
  let agreeSlots ← if step = 1 then r.supply [if oneTime then 7 else 6] else pure []
  let (coins, swaps) ← if step = 1 then do
      let identity ← src.identitySwaps
      let base ← r.stashElems ((← r.randomM 32).map (swapCoins r.me))
      let ratchet ← r.stashElems ((← r.randomM 32).map (swapCoins r.me))
      pure ((fun (s : Receive.Scalar) => match s with
        | .identity => 0
        | .fresh 0 => base
        | .fresh _ => ratchet
        | .own slot => slot),
        (fun (s : Receive.Scalar) => match s with
        | .identity => some identity
        | _ => none))
    else pure ((fun _ => 0), (fun _ => none))
  return { liftPool, checkPool, agreePool, recover := { recover }, check1 := { check }, check2 := { check },
           agree := { coins, swaps }, liftSlots, checkSlots, agreeSlots }

/-- Run one refresh operation: the step's script on the runner, then its commit (table, state). -/
def runStep {Sc : Type} {α : Type} (r : Runner) (src : Sources Sc) (s : Refs)
    (f : Contacts.Table → Refresh.RState → Refresh.RStep α) : M α := do
  let t ← src.table.get
  let st ← get s.state
  let step := f t st
  let a ← r.run step.script
  let (t', st') := step.commit a
  src.table.set t'
  set s.state st'
  return a

/-- A fresh buffer id (shared with S12's buffers). -/
def bufferId {Sc : Type} (src : Sources Sc) : M Nat := do
  let b ← get src.tls.buffers
  set src.tls.buffers { b with next := b.next + 1 }
  return b.next

/-! ## The functions -/

/-- **The refresh functions from the scripts.** -/
def scriptApi {Sc : Type} (r : Runner) (src : Sources Sc) (s : Refs) : Api where
  fetch contact payloadAt offsets mask frame := do
    insist (mask.length == 4 && !frame.isEmpty) "bundle fetch unavailable"
    let t ← src.table.get
    let some e := t.find? contact | throw "bundle fetch unavailable"
    insist e.state.isSome "bundle fetch unavailable"
    let id ← bufferId src
    let f : Fetch := ⟨contact, payloadAt, offsets.getD 0 0, offsets.getD 1 0, toB8 frame, toB8 mask⟩
    set s.fetches ((id, f) :: (← get s.fetches))
    return ⟨id⟩
  take handle offset count := do
    let b ← get src.tls.buffers
    let some (.received _ content _ _) := b.find? handle | throw "bundle take"
    let _ ← runStep r src s fun t st => Refresh.opTake t st content offset count
  drop := do
    set s.fetches []
    runStep r src s fun t st => Refresh.opDrop t st
  shape := do
    match ← runStep r src s fun t st => Refresh.opShape t st r.loaded with
    | none => return none
    | some flags => return some (Reveal.bundleShape flags)
  establish contact registration index devices step at_ _slots widths := do
    let acct ← src.account
    let entropy ← r.stashBits ((← r.randomM 32).map fun b => bitsOf (toB8 b))
    let rc ← curveFor r src (← get s.state) index step
    let (status, _) ← runStep r src s fun t st =>
      Refresh.opEstablish (Join.refreshOps rc) acct t st contact registration index devices step at_ widths entropy
    -- J13: the step's slots (its supplies, the fresh scalars' coins, the entropy) are released.
    r.release ([entropy, rc.agree.coins (.fresh 0), rc.agree.coins (.fresh 1)] ++
      (rc.liftSlots ++ rc.checkSlots ++ rc.agreeSlots).map (·.1))
    return Reveal.deviceStatus [UInt8.ofNat status]
  scratchSeal contact version := do
    let acct ← src.account
    let (_, sealed) ← runStep r src s fun t st => Refresh.opScratchSeal t st contact acct.cert (toB8 version)
    let out := ofB8 sealed
    insist (out.length > 16) "invalid sealed device list"
    return Reveal.sealedBlob out
  scratchCommit contact := runStep r src s fun t st => Refresh.opCommit t st contact

/-- **Seal a pending fetch**, if `id` is one: `Refresh.fetchScript` (checks as `opFetch`) with the
send direction's traffic key and the record's sequence, then S12's shares, half and tag
(`TlsBackend.sealPhases`); the request is dropped (sealed once). -/
def sealFetch {Sc : Type} (r : Runner) (src : Sources Sc) (s : Refs) (id sequence size padding : Nat) :
    M (Option Bytes) := do
  let fs ← get s.fetches
  match fs.lookup id with
  | none => return none
  | some f =>
    insist (padding == 0 && size == f.frame.length) "fetch padding"
    set s.fetches (fs.filter (·.1 != id))
    let t ← src.table.get
    let some e := t.find? f.contact | throw "bundle fetch unavailable"
    let some state := e.state | throw "bundle fetch unavailable"
    let some d := (← get src.tls.conn).send | throw "no sending keys"
    let wire ← TlsBackend.sealPhases r.tls src.tls
      (fun n => Refresh.fetchScript n d.traffic state (seqBytes sequence) f.frame f.mask f.payloadAt f.uuidAt f.keyAt) 7
    return some wire

end TlsMpc.Node.Flows.RefreshBackend
