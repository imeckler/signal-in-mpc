import TlsMpc.Node.Config
import TlsMpc.Node.Flows.RefreshBackend
import TlsMpc.Node.Flows.Upgrade
import TlsMpc.Node.Flows.UpgradeAuth
import TlsMpc.Node.Flows.ContactsPrepare
import TlsMpc.Node.Flows.ContactsAdmit
import TlsMpc.Node.Flows.Masks
import TlsMpc.Node.Flows.Ceremony

/-!
# The selection: legacy operations or Lean scripts, flow group by flow group (agreed)

The flow functions (`TlsMpc/Node/Flow.lean`, implemented in `Flows/*Legacy.lean`) consult the
worker's `overrides` (`Flows/Context.lean`) first; this module fills them, for the flow groups the
AGREED setting `SIGNAL_SCRIPTS` names (`Config.Agreed.scripts`, compared between the two controllers
at session start), from ONE script runner per session (`Flows/Runner.lean`: one `Counters`, one
mask pool, one store). The default, no group, leaves every override `none`: every flow is the legacy
operation, exactly as before. No caller changes: `Worker.startWith` returns the same `Flow.Worker`.

THE ONE LINE `Main.session` NEEDS (not made here: `TlsMpc/Node/Main.lean` and `Session/*` are being
refactored on the main line) — replace `Flow.Worker.start running.rpc ch.random` by

    Flow.Worker.startWith running.rpc ch.random (← natural party) config.agreed config.ceremony.isSome
      (fun _ => true) (fun _ => none)

(the last two: the kernels and the V3 programs' mask counts the worker loaded, from its manifest;
`fun _ => true` makes an unloaded receive kernel abort the session instead of refusing the message,
so pass the manifest's names when the receive scripts are switched on).

THE GROUPS (`Config.scriptNames`), what each replaces, what it needs, and whether it is available:

  | group | flow functions | needs | available |
  |---|---|---|---|
  | `random` | `Random.joint` (op 33) | nothing | yes (exchanges only, no engine call) |
  | `masks` | the S10 pool (`Masks.generate`, refilled on demand) | the V3 `field-*` programs | yes (needs the re-export to run) |
  | `tls` | `Tls.handshake`'s and `Tls.application`'s backends, `publicBuffer`, `recordLength`, `revealRange`, the script half of `Server.reset` (ops 1-8, 12-16, 30, 43, 91) | `masks` (split ECDH's F2W); CLOSED only with every group of `closedSet` (J22, `stranded`) | yes (needs the re-export: split ECDH's V3 programs) |
  | `upgrade` | `Upgrade.anonymous` (op 45) | `tls` (op 45 also sets the legacy service's receive state, `Upgrade.lean`; with the record layer in Lean nothing reads it) | yes |
  | `contacts` | `Contacts.key/load/loadDevices/seal/evict/assign/admitTest` (ops 36-38, 40, 52, 63; 44 TEST, J23) | the contact set below | yes |
  | `account` | `Account.key/credentials/load/seal/admitTest` (ops 53, 47, 55, 54, 46), `Upgrade.authenticated` (op 32, `Flows/UpgradeAuth.lean`) | the contact set | yes (J11) |
  | `curve` | `Curve.prepareContacts` (op 66, `Flows/ContactsPrepare.lean`) | the contact set | yes (F32) |
  | `send` | `Send.seal/sealDevices/request/requestDevices` (ops 41, 42, 61, 62) | the contact set | yes |
  | `receive` | `Receive.take/drop/openFirst/session` (ops 48-51) | the contact set | yes (J8) |
  | `refresh` | `Refresh.*` (ops 56-60, 64, 65) | the contact set | yes (J8, J12) |
  | `ceremony` | `Ceremony.secrets/register` (ops 80, 81, `Flows/Ceremony.lean`, S16) | `tls`, `masks`, `random`, `upgrade` | yes |

THE CONTACT SET (`contactSet`: `contacts`, `account`, `curve`, `send`, `receive`, `refresh`) switches
AS ONE: its handles cannot be shared with the legacy library (the legacy worker's contact table,
account and caches are not the script engine's handles), so every group of the set needs every
other one, and `tls` and `masks` (the record layer seals the requests; every curve step converts).

`check` refuses a selection that names an unavailable group or misses a needed one, at session
start, with the reason. Every override is written (the switch is a setting, not a code change).
J22: `check` also refuses a selection with `tls` that leaves a legacy operation needing the legacy
library's TLS phase (`tlsDependent`, `stranded`) without its script; for every session but a
registration ceremony the smallest accepted selection with `tls` is all ten groups (`closedSet`,
`tls_needs_closedSet`); for a ceremony session it is all eleven (`ceremonySet`,
`ceremony_needs_ceremonySet`; without `ceremony`: `check_ceremony_tls`).

What remains OUTSIDE this module for the contact set to RUN (STACK_NOTES section 6): the V3
field-program re-export and its pins; `Main.session` calling `Worker.startWith` (J9); the
manifest's kernel names (`loaded`, so a receive kernel the manifest lacks refuses the message) and
the V3 programs' mask counts (`programMasks`: `xeddsa-check`, `xeddsa-recover`, `receive-torsion`
for receive and refresh) passed to `Worker.startWith`.

The `Reveal.*` wrappers: the script implementations make their `Opened` values with the SAME
`Reveal.*` functions as the legacy ones (the reveal list does not change, plan 4.3). STACK_NOTES J4,
chosen: `scripts/lint_node.py`'s `flow-calls` allowlist is widened to the script backends
(`Flows/*Backend.lean`), the runner and this module, rather than adding script-side makers to
`Reveal.lean` (they would duplicate every maker and its bound for the same opened value).

No I/O primitive (`IO.Ref` only); no emitter imports this module.
-/

namespace TlsMpc.Node.Flows.Select

open TlsMpc.Node.Engine
open TlsMpc.TlsClient (M insist)
open TlsMpc.Node.Flows.Contacts (B8 bitsOf bytesOf)
open TlsMpc.Node.Flows.Runner (Runner)
open TlsMpc.Node.Flows.TlsBackend (toB8 ofB8)
open TlsMpc.FieldDag (F)

/-! ## What a selection needs -/

/-- The groups that switch together (module doc: no handle sharing with the legacy library). -/
def contactSet : List String := ["contacts", "account", "curve", "send", "receive", "refresh"]

/-- The groups a group needs selected with it (module doc). -/
def requires (g : String) : List String :=
  if contactSet.contains g then contactSet ++ ["tls", "masks"] else
  match g with
  | "tls" => ["masks"]
  | "upgrade" => ["tls"]
  -- S16: ops 80, 81. The request is sealed by the scripted record layer (`tls`). Everything else a
  -- ceremony session needs selected with it is not asserted here but follows from the closure
  -- (J22, `stranded`; PROOF_GAPS K12): `ceremony_needs_ceremonySet`.
  | "ceremony" => ["tls"]
  | _ => []

/-- The groups whose script implementation cannot run yet, and why: none since J8, J11, J12, F32. -/
def unavailable : List (String × String) := []

/-! ## J22: the legacy operations that need the legacy library's TLS state

Every legacy service operation of `tls_worker_v3.cpp` requires the ACTIVE connection's legacy TLS
phase to be `retired` (`need(phase==Phase::retired && service, …)`; op 91 through `ea_legacy_reset`,
`legacy_abi.cpp`). Only the legacy handshake (ops 1-7, `Tls.legacyBackend`) moves that phase; with
`tls` selected the handshake is a script and the legacy phase of every connection stays `fresh`, so
every legacy operation below is refused by the legacy library. A selection with `tls` is therefore
CLOSED only if every one of them that the session can issue is replaced by a selected script. Which
operations a session can issue depends on its kind, part of the agreed settings
(`Config.agreedText`'s `ceremony=`): a registration ceremony session (`Session/Ceremony.lean`, both
stages: `register` issues 33, 45, 80, 81 and the record layer's; `certificate` issues 47, 32 and the
record layer's) issues no contact, account-state, curve, send, receive or refresh operation and no
op 91; every other session issues no ceremony operation. No C++ bridges script state into the legacy
library (the owner's rule): the selection refuses what it cannot close. STACK_NOTES.md section 10 has
the same table with each script's file. -/

/-- A legacy worker operation that needs the legacy library's retired TLS phase: its code, the flow
function that issues it, the selection name whose script replaces it (`none`: no script yet), and
whether a service session (send, receive, the long-lived session) and a registration ceremony
session can issue it. -/
structure LegacyOp where
  code : Nat
  flow : String
  group : Option String
  inService : Bool
  inCeremony : Bool
  deriving DecidableEq, Repr

/-- Whether a session of this kind (`ceremony`: a registration ceremony) can issue the operation. -/
def LegacyOp.issued (o : LegacyOp) (ceremony : Bool) : Bool := if ceremony then o.inCeremony else o.inService

/-- **The table** (STACK_NOTES.md section 10; S16_NOTES.md section 4 for the ceremony's). -/
def tlsDependent : List LegacyOp :=
  [⟨12, "Tls.application (open record)", some "tls", true, true⟩,
   ⟨13, "Tls.application (seal record)", some "tls", true, true⟩,
   ⟨14, "Tls.application (seal control)", some "tls", true, true⟩,
   ⟨15, "Tls.application (rotate send key)", some "tls", true, true⟩,
   ⟨16, "Tls.application (rotate receive key)", some "tls", true, true⟩,
   ⟨30, "Tls.publicBuffer", some "tls", true, true⟩,
   ⟨43, "Tls.recordLength/revealRange", some "tls", true, true⟩,
   ⟨91, "Server.reset", some "tls", true, false⟩,
   ⟨33, "Random.joint", some "random", true, true⟩,
   ⟨45, "Upgrade.anonymous", some "upgrade", true, true⟩,
   ⟨32, "Upgrade.authenticated", some "account", true, true⟩,
   ⟨36, "Contacts.key", some "contacts", true, false⟩,
   ⟨37, "Contacts.load", some "contacts", true, false⟩,
   ⟨38, "Contacts.seal", some "contacts", true, false⟩,
   ⟨40, "Contacts.evict", some "contacts", true, false⟩,
   ⟨44, "Contacts.admitTest (TEST)", some "contacts", true, false⟩,
   ⟨52, "Contacts.assign", some "contacts", true, false⟩,
   ⟨63, "Contacts.loadDevices", some "contacts", true, false⟩,
   ⟨46, "Account.admitTest (TEST)", some "account", true, false⟩,
   ⟨47, "Account.credentials", some "account", true, true⟩,
   ⟨53, "Account.key", some "account", true, false⟩,
   ⟨54, "Account.seal", some "account", true, false⟩,
   ⟨55, "Account.load", some "account", true, false⟩,
   ⟨66, "Curve.prepareContacts", some "curve", true, false⟩,
   ⟨41, "Send.seal", some "send", true, false⟩,
   ⟨42, "Send.request", some "send", true, false⟩,
   ⟨61, "Send.sealDevices", some "send", true, false⟩,
   ⟨62, "Send.requestDevices", some "send", true, false⟩,
   ⟨48, "Receive.take", some "receive", true, false⟩,
   ⟨49, "Receive.drop", some "receive", true, false⟩,
   ⟨50, "Receive.openFirst", some "receive", true, false⟩,
   ⟨51, "Receive.session", some "receive", true, false⟩,
   ⟨56, "Refresh.fetch", some "refresh", true, false⟩,
   ⟨57, "Refresh.take", some "refresh", true, false⟩,
   ⟨58, "Refresh.drop", some "refresh", true, false⟩,
   ⟨59, "Refresh.shape", some "refresh", true, false⟩,
   ⟨60, "Refresh.establish", some "refresh", true, false⟩,
   ⟨64, "Refresh.scratchSeal", some "refresh", true, false⟩,
   ⟨65, "Refresh.scratchCommit", some "refresh", true, false⟩,
   ⟨80, "Ceremony.secrets", some "ceremony", false, true⟩,
   ⟨81, "Ceremony.register", some "ceremony", false, true⟩]

/-- Whether a selected script replaces the operation. -/
def scripted (names : List String) (o : LegacyOp) : Bool :=
  match o.group with
  | some g => names.contains g
  | none => false

/-- **The operations a selection strands**: with `tls` selected, every operation of the table this
session can issue (`ceremony`: the session is a registration ceremony) that no selected script
replaces. Without `tls` the legacy handshake runs and nothing is stranded. -/
def stranded (names : List String) (ceremony : Bool) : List LegacyOp :=
  if names.contains "tls" then tlsDependent.filter fun o => o.issued ceremony && !scripted names o
  else []

/-- The refusal's text: each stranded operation, and the names to select (or "S16"). -/
def strandedMessage (ops : List LegacyOp) : String :=
  let want := (ops.filterMap (·.group)).eraseDups
  "SIGNAL_SCRIPTS: tls owns every connection's TLS state, so the legacy library's TLS phase never reaches " ++
  "retired, and these legacy operations of this session would be refused: " ++
  String.intercalate ", " (ops.map fun o => s!"op {o.code} {o.flow}" ++
    (match o.group with
     | some g => s!" (select {g})"
     | none => " (no script yet)")) ++
  (if want.isEmpty then "" else s!"; select also: {String.intercalate "," want}")

/-- The named groups that are unavailable, with the reason. -/
def unavailableNamed (names : List String) : List (String × String) :=
  names.filterMap fun n => (unavailable.find? (·.1 == n)).map fun p => (n, p.2)

/-- The (group, needed group) pairs a selection misses. -/
def needsMissing (names : List String) : List (String × String) :=
  names.flatMap fun n => ((requires n).filter fun m => !names.contains m).map fun m => (n, m)

/-- **A selection is accepted** when every group it names is available, every group a named group
needs is named too, and (J22) it strands no legacy operation of this session (`stranded`). -/
def check (names : List String) (ceremony : Bool) : Except String Unit :=
  match unavailableNamed names with
  | (n, why) :: _ => .error s!"SIGNAL_SCRIPTS: {n} is not available: {why}"
  | [] =>
    match needsMissing names with
    | (n, m) :: _ => .error s!"SIGNAL_SCRIPTS: {n} needs {m} selected too"
    | [] =>
      match stranded names ceremony with
      | [] => .ok ()
      | ops => .error (strandedMessage ops)

theorem check_ok (names : List String) (ceremony : Bool) (h : (check names ceremony).toBool = true) :
    unavailableNamed names = [] ∧ needsMissing names = [] ∧ stranded names ceremony = [] := by
  unfold check at h
  cases h1 : unavailableNamed names with
  | cons p ps =>
    obtain ⟨n, why⟩ := p
    simp [h1, Except.toBool] at h
  | nil =>
    cases h2 : needsMissing names with
    | cons p ps =>
      obtain ⟨n, m⟩ := p
      simp [h1, h2, Except.toBool] at h
    | nil =>
      cases h3 : stranded names ceremony with
      | cons p ps => simp [h1, h2, h3, Except.toBool] at h
      | nil => exact ⟨rfl, rfl, rfl⟩

/-- **J22, the closure: an accepted selection strands no legacy operation.** If `check` accepts a
selection with `tls`, every legacy operation of the table that this session can issue is replaced by
a script of a selected group. -/
theorem check_closed (names : List String) (ceremony : Bool) (h : (check names ceremony).toBool = true)
    (htls : names.contains "tls" = true) :
    ∀ o ∈ tlsDependent, o.issued ceremony = true → ∃ g, o.group = some g ∧ names.contains g = true := by
  intro o ho hk
  have hs := (check_ok names ceremony h).2.2
  simp only [stranded, htls, ↓reduceIte, List.filter_eq_nil_iff] at hs
  have hsc : scripted names o = true := by
    have := hs o ho
    revert this
    cases scripted names o <;> simp [hk]
  unfold scripted at hsc
  cases hg : o.group with
  | none => simp [hg] at hsc
  | some g => simp only [hg] at hsc; exact ⟨g, rfl, hsc⟩

/-- An accepted selection names every group a named group needs. -/
theorem check_needs (names : List String) (ceremony : Bool) (h : (check names ceremony).toBool = true) :
    ∀ n ∈ names, ∀ m ∈ requires n, names.contains m = true := by
  intro n hn m hm
  have hs := (check_ok names ceremony h).2.1
  simp only [needsMissing, List.flatMap_eq_nil_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff] at hs
  have := hs n hn m hm
  simpa using this

/-- **The closed selection with `tls`** for every session that is not a registration ceremony: the
contact set, `tls`, `masks`, and the two groups whose legacy operations need the legacy TLS phase too,
`random` (op 33) and `upgrade` (op 45). -/
def closedSet : List String := contactSet ++ ["tls", "masks", "random", "upgrade"]

/-- **J22: the smallest closed selection containing `tls` is all ten groups** (`closedSet`): any
selection with `tls` that `check` accepts, for a session that is not a ceremony, contains every
group of `closedSet`. -/
theorem tls_needs_closedSet (names : List String) (h : (check names false).toBool = true)
    (htls : names.contains "tls" = true) : ∀ g ∈ closedSet, names.contains g = true := by
  have hc := check_closed names false h htls
  have via : ∀ code flow g b, (⟨code, flow, some g, true, b⟩ : LegacyOp) ∈ tlsDependent →
      names.contains g = true := by
    intro code flow g b hm
    obtain ⟨g', hg', hc'⟩ := hc _ hm (by simp [LegacyOp.issued])
    simp only [Option.some.injEq] at hg'
    subst hg'
    exact hc'
  intro g hg
  simp only [closedSet, contactSet, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact via 36 "Contacts.key" _ false (by decide)
  · exact via 53 "Account.key" _ false (by decide)
  · exact via 66 "Curve.prepareContacts" _ false (by decide)
  · exact via 41 "Send.seal" _ false (by decide)
  · exact via 48 "Receive.take" _ false (by decide)
  · exact via 56 "Refresh.fetch" _ false (by decide)
  · exact htls
  · have := check_needs names false h "tls" (by simpa using htls) "masks" (by decide)
    exact this
  · exact via 33 "Random.joint" _ true (by decide)
  · exact via 45 "Upgrade.anonymous" _ true (by decide)

/-- **The closed selection is accepted** (any session but a ceremony). -/
theorem check_contactSet : (check closedSet false).toBool = true := by decide

/-- **…and only whole**: without any one of its ten groups it is refused. -/
theorem check_contactSet_partial :
    ∀ g ∈ closedSet, (check (closedSet.erase g) false).toBool = false := by
  decide

/-- **J22: the selection the stack accepted before is not closed**: the contact set with `tls` and
`masks` only strands op 33 (`Random.joint`) and op 45 (`Upgrade.anonymous`), so it is refused. -/
theorem check_contactSet_unclosed : (check (contactSet ++ ["tls", "masks"]) false).toBool = false := by decide

/-- **J22: no selection with `tls` but without `ceremony` is accepted for a registration ceremony
session** (ops 80 and 81, `Ceremony.secrets` / `Ceremony.register`, would be stranded). Before S16
this read: no selection with `tls` at all. -/
theorem check_ceremony_tls (names : List String) (htls : names.contains "tls" = true)
    (hno : names.contains "ceremony" = false) : (check names true).toBool = false := by
  cases h : (check names true).toBool with
  | false => rfl
  | true =>
    obtain ⟨g, hg, hc⟩ := check_closed names true h htls ⟨80, "Ceremony.secrets", some "ceremony", false, true⟩
      (by decide) (by simp [LegacyOp.issued])
    simp only [Option.some.injEq] at hg
    subst hg
    rw [hno] at hc
    cases hc

/-- **The closed selection of a registration ceremony session** (K12): `ceremony` and every group of
`closedSet`. Not asserted: it follows from the closure (`ceremony_needs_ceremonySet`): the ceremony's
`certificate` stage issues ops 47 and 32 (`account`, which needs the contact set), its `register`
stage ops 33 and 45 (`random`, `upgrade`), both the record layer's (`tls`, which needs `masks`). -/
def ceremonySet : List String := closedSet ++ ["ceremony"]

/-- **K12: what a ceremony session with `tls` must select follows from the closure**: any accepted
selection with `tls` for a ceremony session contains every group of `ceremonySet`. -/
theorem ceremony_needs_ceremonySet (names : List String) (h : (check names true).toBool = true)
    (htls : names.contains "tls" = true) : ∀ g ∈ ceremonySet, names.contains g = true := by
  have hc := check_closed names true h htls
  have via : ∀ code flow g b, (⟨code, flow, some g, b, true⟩ : LegacyOp) ∈ tlsDependent →
      names.contains g = true := by
    intro code flow g b hm
    obtain ⟨g', hg', hc'⟩ := hc _ hm (by simp [LegacyOp.issued])
    simp only [Option.some.injEq] at hg'
    subst hg'
    exact hc'
  have hacc : names.contains "account" = true := via 47 "Account.credentials" _ true (by decide)
  have viaAcc : ∀ m ∈ requires "account", names.contains m = true :=
    check_needs names true h "account" (by simpa using hacc)
  intro g hg
  simp only [ceremonySet, closedSet, contactSet, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact viaAcc "contacts" (by decide)
  · exact hacc
  · exact viaAcc "curve" (by decide)
  · exact viaAcc "send" (by decide)
  · exact viaAcc "receive" (by decide)
  · exact viaAcc "refresh" (by decide)
  · exact htls
  · exact check_needs names true h "tls" (by simpa using htls) "masks" (by decide)
  · exact via 33 "Random.joint" _ true (by decide)
  · exact via 45 "Upgrade.anonymous" _ true (by decide)
  · exact via 80 "Ceremony.secrets" _ false (by decide)

/-- **The ceremony's closed selection is accepted** for a ceremony session. -/
theorem check_ceremonySet : (check ceremonySet true).toBool = true := by decide

/-- **…and only whole**: without any one of its eleven groups it is refused. -/
theorem check_ceremonySet_partial : ∀ g ∈ ceremonySet, (check (ceremonySet.erase g) true).toBool = false := by
  decide

/-- Without `tls` nothing is stranded (the legacy handshake runs as before). -/
theorem stranded_without_tls (names : List String) (ceremony : Bool) (h : names.contains "tls" = false) :
    stranded names ceremony = [] := by
  unfold stranded
  simp only [h, Bool.false_eq_true, ↓reduceIte]

/-! ## The session's script state -/

/-- Everything the selected script implementations share: the runner (state, store, counters,
pool), the account, the connections' TLS state (S12_NOTES "The Session/Pool change": kept here, in
the flow context, until `Session/Pool` holds it), the send's requests, the receive's and the
refresh's state. -/
structure Session where
  runner : Runner
  account : IO.Ref Account.State
  /-- Op 66's offset states next to the contact table (`ContactsPrepare.Cache`, F32). -/
  prepared : IO.Ref ContactsPrepare.Cache
  conns : IO.Ref (List (Nat × IO.Ref (Tls.Conn JoinBackend.SplitState)))
  buffers : IO.Ref Tls.Buffers
  requests : IO.Ref (List (Nat × SendBackend.Request))
  receive : ReceiveBackend.Refs
  refresh : RefreshBackend.Refs
  /-- `TLS_WORKER_HINTED=1`: op 55 also converts the scalar's hinted bits. -/
  hinted : Bool
  /-- `SIGNAL_RECEIVE_JUMP`. -/
  jump : Nat
  /-- S16: the ceremony's handles between ops 80 and 81 (`Ceremony.State`). -/
  ceremony : IO.Ref Ceremony.State

def get {α : Type} (r : IO.Ref α) : M α := (r.get : IO α)
def set {α : Type} (r : IO.Ref α) (a : α) : M Unit := (r.set a : IO Unit)

def Session.start (r : Runner) (agreed : Config.Agreed) : IO Session := do
  return { runner := r, account := ← IO.mkRef {}, prepared := ← IO.mkRef [], conns := ← IO.mkRef [],
           buffers := ← IO.mkRef {}, requests := ← IO.mkRef [],
           receive := { envelope := ← IO.mkRef none, arrival := ← IO.mkRef none },
           refresh := { state := ← IO.mkRef {}, fetches := ← IO.mkRef [] }, hinted := agreed.hinted,
           jump := ((agreed.receiveJump.bind String.toNat?).getD 0),
           ceremony := ← IO.mkRef {} }

/-- A connection's TLS state (connection 0 when no connection is selected), made on first use. -/
def Session.tlsRefs (s : Session) (connection : Option Nat) : M (TlsBackend.Refs JoinBackend.SplitState) := do
  let i := connection.getD 0
  let cs ← get s.conns
  match cs.lookup i with
  | some c => return { conn := c, buffers := s.buffers }
  | none =>
    let c ← (IO.mkRef {} : IO (IO.Ref (Tls.Conn JoinBackend.SplitState)))
    set s.conns ((i, c) :: cs)
    return { conn := c, buffers := s.buffers }

/-! ## S10: the mask pool -/

/-- A uniform field element and its 255 bits, from 64 random bytes (statistical distance below
2⁻²⁵⁰ from uniform). -/
def candidate (b : Bytes) : F := TlsMpc.FieldDag.ofNat (Engine.fromLE b)

/-- **Generate `p`'s pool** (`Masks.generate`): this party's `M` canonical random candidates (bits,
elements, coins) and its challenge nonces and values in fresh store slots, the handle blocks from
the counters; the new masks join the session's pool. -/
def generatePool (r : Runner) (p : Masks.Params) : M Unit := do
  let raw ← r.randomM (64 * p.M)
  let cands : Secret (List F) := raw.map fun b => (List.range p.M).map fun j => candidate ((b.drop (64 * j)).take 64)
  let bits ← r.stashBits (cands.map fun cs => (cs.map fun c => Conv.word c.val).flatten)
  let elems ← r.stashElems cands
  let coins ← r.next.get
  for j in List.range p.M do
    let _ ← r.stashElems (cands.map fun cs => (Conv.word (cs.getD j 0).val).map X25519.bitValue)
  let cutNonce ← r.stashBytes (← r.randomM 32)
  let cutValue ← r.stashBytes (← r.randomM 32)
  let bucketNonce ← r.stashBytes (← r.randomM 32)
  let bucketValue ← r.stashBytes (← r.randomM 32)
  let b ← r.allocB (Masks.boolIds p)
  let f ← r.allocF (Masks.fieldIds p)
  let coinSlots := (List.range p.M).map (coins + ·)
  let pool ← r.runReleasing (Masks.generate p b f r.hash r.me ⟨bits, elems, coins, cutNonce, cutValue, bucketNonce, bucketValue⟩)
    ([bits, elems, cutNonce, cutValue, bucketNonce, bucketValue] ++ coinSlots)
  let st ← Runner.get r.state
  Runner.set r.state { st with pool := { words := st.pool.words ++ pool.words, bits := st.pool.bits ++ pool.bits } }

/-- **Refill the pool** until it holds `words` word masks and `bits` bit pairs (the deployed profile
`N = 16`, buckets of 22; as many bit blocks as needed, at most 16 per generation). -/
def refill (r : Runner) (words bits : Nat) : M Unit := do
  for _ in List.range 64 do
    let st ← Runner.get r.state
    if words ≤ st.pool.words.length && bits ≤ st.pool.bits.length then return
    let blocks := min 16 ((bits - min bits st.pool.bits.length + 254) / 255)
    let some p := Masks.profile 16 blocks | throw "mask profile"
    generatePool r p
  throw "mask pool refill bound"

/-! ## The overrides, group by group -/

/-- `random`: P-RAND's commit-then-open (`Flows/Random.lean`). -/
def randomJoint (r : Runner) : M (Opened .jointRandom Bytes) := do
  let nonce ← r.stashBytes (← r.randomM 32)
  let value ← r.stashBytes (← r.randomM 32)
  let random ← r.runReleasing (Random.joint r.hash r.me nonce value) [nonce, value]
  insist (random.length == 32) "invalid joint randomness"
  return Reveal.jointRandom random

/-- `upgrade`: op 45 (`Flows/Upgrade.lean`). -/
def upgradeAnonymous (r : Runner) : M (Opened .upgradeNonce (Bytes × Bytes)) := do
  let nonce ← r.stashBytes (← r.randomM 32)
  let value ← r.stashBytes (← r.randomM 32)
  let upgrade ← r.runReleasing (Upgrade.publicUpgrade r.hash r.me nonce value) [nonce, value]
  insist (upgrade.length == 44) "invalid public upgrade receipt"
  return Reveal.upgradeNonce (upgrade.take 16) (upgrade.drop 16)

/-- A contact-table step on the runner's table: its script, then its commit; the slots it was given
are released after it (J13). -/
def tableStep {α : Type} (r : Runner) (f : Contacts.Table → Contacts.Step α) (slots : List Nat := []) : M α := do
  let t ← r.table.get
  let st := f t
  let a ← r.runReleasing st.script slots
  r.table.set (st.commit a)
  return a

/-- The stored blob `version ‖ check ‖ ciphertext`. -/
def splitStored (stored : Bytes) : B8 × B8 × B8 :=
  (toB8 (stored.take 8), toB8 ((stored.drop 8).take 16), toB8 (stored.drop 24))

/-- The account state with the session's counters (one `Counters`), and its commit. -/
def withCounters {α : Type} (s : Session) (f : Account.State → M (α × Account.State)) : M α := do
  let st ← Runner.get s.runner.state
  let a ← get s.account
  let (x, a') ← f { a with ctr := st.table.ctr }
  let st' ← Runner.get s.runner.state
  Runner.set s.runner.state { st' with table := { st'.table with ctr := a'.ctr } }
  set s.account a'
  return x

/-- **J8: the agreements' scalars.** The identity scalar's swap bits are the account's field handles
(`Account.State.identity`, op 55 / op 46): no coins slot. An `own` or `fresh` scalar's slot is the
coins slot the IO side stashed for it (`ReceiveBackend.session`, `RefreshBackend.curveFor`). -/
def agreeSlots (s : Session) : M Join.AgreeSlots := do
  let a ← get s.account
  let some ids := a.identity | throw "account not loaded (no identity swap bits)"
  return { coins := fun sc => match sc with
             | .own x => x
             | .fresh x => x
             | .identity => 0,
           swaps := fun sc => match sc with
             | .identity => some ids
             | _ => none }

/-- Run a state-threaded script whose agreements take `counts` from the supply (J1: new slots). -/
def runAgree {α : Type} (s : Session) (counts : List Nat) (g : Receive.Gen α) : M α := do
  let r := s.runner
  let supply ← r.supply counts
  let a ← ReceiveBackend.runWith r.receive supply g
  r.release (supply.map (·.1))
  return a

/-- **J12: the account's sender key word**, made once (`ContactsPrepare.senderPublicG`: X25519 of the
identity with 9, as the C++'s `agreement_word(identity, 9)`) and kept in the account state. -/
def senderPublic (s : Session) : M BoolH := do
  if let some w := (← get s.account).senderPublic then return w
  let sl ← agreeSlots s
  refill s.runner 2 0
  let w ← runAgree s [1] (ContactsPrepare.senderPublicG sl)
  set s.account { (← get s.account) with senderPublic := some w }
  return w

/-- The account's handles the refresh reads (J12: the sender key word from the account state). -/
def refreshAccount (s : Session) : M Refresh.Account := do
  let a ← get s.account
  let some (certificate, cert) := a.certificate | throw "account not loaded"
  return { certificate, cert, senderPublic := ← senderPublic s }

/-- **F32: one contact's preparation** (`ContactsPrepare.prepareOneG`) and its commit: fresh store
slots for the offset agreement (this party's random scalar share: its coins and its K₀ half; one
random element; 2031 mask contributions; a commitment nonce), one supply slot for the static
agreement's quotient, the identity's swap-bit handles. -/
def prepareOne (s : Session) (id : Nat) (state : BoolH) : M Unit := do
  let r := s.runner
  let a ← get s.account
  let some (cert, certLen) := a.certificate | throw "prepare unavailable"
  let sl ← agreeSlots s
  refill r 4 0
  let scalar ← r.randomM 32
  let os : Curve.OffsetSlots :=
    { r := ← r.stashElems (← JoinBackend.elems r.tls 1),
      bits := ← r.stashElems (scalar.map Curve.offsetCoins),
      masks := ← r.stashElems (← JoinBackend.elems r.tls Curve.prepMasks),
      nonce := ← r.stashBytes (← r.randomM 32),
      share := ← r.stashBytes (scalar.map Curve.offsetShare) }
  let p ← runAgree s [1] (ContactsPrepare.prepareOneG r.hash r.me cert certLen sl os state)
  r.release [os.r, os.bits, os.masks, os.nonce, os.share]
  let st ← Runner.get r.state
  let (t', c') := ContactsPrepare.commit st.table (← get s.prepared) id p
  Runner.set r.state { st with table := t' }
  set s.prepared c'

/-- A contact's prepared values, preparing it first when it is loaded and not prepared (the C++'s
`prepare(c)` on a first send). -/
def preparedOf (s : Session) (id : Nat) : M (Option ContactsPrepare.Prepared) := do
  let st ← Runner.get s.runner.state
  let cache ← get s.prepared
  if let some p := ContactsPrepare.prepared? st.table cache id then return some p
  match ContactsPrepare.needs st.table cache id with
  | none => return none
  | some state =>
    prepareOne s id state
    let st' ← Runner.get s.runner.state
    return ContactsPrepare.prepared? st'.table (← get s.prepared) id

/-- **J11: op 32 on the script account state** (`UpgradeAuth.authenticated`): the request's handle
is kept as a buffer of the connection (sealed by the record layer like any buffer, S12). -/
def upgradeAuthenticated (s : Session) (c : Option Nat) (state : Nat) :
    M (TlsWorker.BufferHandle × Nat × Opened .upgradeAccept Bytes) := do
  let r := s.runner
  insist (state == 1) "provider upgrade"
  let some cr := UpgradeAuth.credsOf (← get s.account) | throw "upgrade unavailable"
  let nonce ← r.stashBytes (← r.randomM 32)
  let value ← r.stashBytes (← r.randomM 32)
  let n ← r.allocB 3
  let (h, accept) ← r.runReleasing (UpgradeAuth.authenticated r.hash r.me nonce value n cr) [nonce, value]
  insist (accept.length == 28) "invalid upgrade receipt"
  let refs ← s.tlsRefs c
  let (id, b') := (← get refs.buffers).add (.publicBytes h UpgradeAuth.requestBytes)
  set refs.buffers b'
  return (⟨id⟩, UpgradeAuth.requestBytes, Reveal.upgradeAccept accept)

/-- **S16: op 80** (`Ceremony.secretsStep`): this party's seed, mask and recovery half from its own
randomness (rule 5) into fresh store slots, the script, the slots released; the two kept handles go
to the ceremony state; the reply is this party's shares (`Ceremony.shareOf`, the C++'s reply),
computed from its own mask and recovery half and the opened masked password. -/
def ceremonySecrets (s : Session) : M (Secret Bytes) := do
  let r := s.runner
  let st ← get s.ceremony
  insist (!st.made) "ceremony secrets unavailable"
  let seed ← r.randomM Ceremony.seedBytes
  let mask ← r.randomM Ceremony.passwordBytes
  let recovery ← r.randomM Ceremony.recoveryBytes
  let seedSlot ← r.stashBits (seed.map fun b => bitsOf (toB8 b))
  let maskSlot ← r.stashBits (mask.map fun b => bitsOf (toB8 b))
  let recoverySlot ← r.stashBits (recovery.map fun b => bitsOf (toB8 b))
  let n ← r.allocB 11
  let m ← r.runReleasing (Ceremony.secretsStep st n seedSlot maskSlot recoverySlot) [seedSlot, maskSlot, recoverySlot]
  set s.ceremony (Ceremony.State.afterSecrets m)
  return Secret.zipWith (fun mk rc => ofB8 (Ceremony.shareOf r.me (toB8 mk) (toB8 rc) m.masked)) mask recovery

/-- **S16: op 81** (`Ceremony.registerStep`): the secrets handle tail ‖ password ‖ recovery, kept as a
request buffer (`SendBackend.Request`) whose record seal is `Send.requestCtrScript` with
`ceremony-register-ctr SIZE PAYLOAD AUTH TAIL RECOVERY` (sealed by the record layer's
`sealApplication`, as op 42's requests). `find`'s ranges are checked here. -/
def ceremonyRegister (s : Session) (payloadAt : Nat) (offsets : List Nat) (mask tail frame : Bytes) :
    M TlsWorker.BufferHandle := do
  let r := s.runner
  let st ← get s.ceremony
  let authAt := offsets.getD 0 0
  let recoveryAt := offsets.getD 1 0
  insist (mask.length == 4 && offsets.length == 2 &&
    Ceremony.registerOk frame.length payloadAt authAt tail.length recoveryAt) "ceremony register unavailable"
  let n ← r.allocB 2
  let conv ← r.run (Ceremony.registerStep st n (toB8 tail))
  set s.ceremony st.afterRegister
  let b ← get s.buffers
  set s.buffers { b with next := b.next + 1 }
  let rq : SendBackend.Request :=
    ⟨conv, Ceremony.registerName frame.length payloadAt authAt tail.length recoveryAt, toB8 frame, toB8 mask⟩
  set s.requests ((b.next, rq) :: (← get s.requests))
  return ⟨b.next⟩

/-- **The overrides of the selected groups.** -/
def overrides (s : Session) (names : List String) : Flow.Overrides :=
  let r := s.runner
  let on (n : String) {α : Type} (a : α) : Option α := if names.contains n then some a else none
  let ka := JoinBackend.keyAgreement r.tls r.field
  let sendRefs (c : Option Nat) : M (SendBackend.Refs JoinBackend.SplitState) := do
    return { table := r.table, account := s.account, requests := s.requests, tls := ← s.tlsRefs c }
  -- F32, J12: the send's cached curve values from op 66's glue and the account state.
  let sendCurve : SendBackend.Curve := JoinBackend.sendCurve r.tls r.field
    { offsets := fun id => do
        refill r 2 0
        return (← preparedOf s id).map (·.offset),
      statics := fun id => do return (← preparedOf s id).map (·.static),
      senderPublic := senderPublic s }
  let refreshSources (c : Option Nat) : M (RefreshBackend.Sources JoinBackend.SplitState) := do
    return { table := r.table, account := refreshAccount s,
             identitySwaps := do
               let some ids := (← get s.account).identity | throw "account not loaded (no identity swap bits)"
               return ids,
             tls := ← s.tlsRefs c }
  let receiveApi : M ReceiveBackend.Api := do
    let refs ← s.tlsRefs none
    let certificate : M (BoolH × Nat) := do
      let a ← get s.account
      let some c := a.certificate | throw "account not loaded"
      return c
    let revealed (h : Nat) : M (BoolH × Nat) := do
      refill r 32 510
      TlsBackend.revealed r.tls refs h
    -- J8: the joined agreements with the identity's swap-bit handles (no coins slot for it).
    let curve (op : ReceiveBackend.Op) : M (Receive.Curve × List (Nat × Nat)) := do
      refill r 32 510
      let sl ← agreeSlots s
      ReceiveBackend.programCurve r.receive
        ⟨Join.receiveAgree sl, Join.receiveAgreeKinds, Join.receiveAgree_reveals sl, fun n => [n]⟩ op
    return ReceiveBackend.scriptApi r.receive curve revealed certificate s.jump s.receive
  { randomJoint := on "random" (randomJoint r)
    upgradeAnonymous := on "upgrade" (upgradeAnonymous r)
    tlsBackend := on "tls" fun c =>
      -- The certificate check stays local, as the legacy backend's (`Rpc.authenticate`).
      let hs (refs : TlsBackend.Refs JoinBackend.SplitState) :=
        TlsBackend.scriptBackend r.tls ka r.worker.pipe.authenticate refs
      { begin := do refill r 4 0; (hs (← s.tlsRefs c)).begin
        derive := fun k peer hash => do refill r 4 0; (hs (← s.tlsRefs c)).derive k peer hash
        openHandshake := fun k sq wire => do (hs (← s.tlsRefs c)).openHandshake k sq wire
        authenticate := fun h ch sc hh sg => do (hs (← s.tlsRefs c)).authenticate h ch sc hh sg
        verifyFinished := fun k hh m => do (hs (← s.tlsRefs c)).verifyFinished k hh m
        finish := fun k sh ch cert => do (hs (← s.tlsRefs c)).finish k sh ch cert
        retire := fun k a => do (hs (← s.tlsRefs c)).retire k a
        abort := do (hs (← s.tlsRefs c)).abort }
    tlsPublicBuffer := on "tls" fun c bytes => do TlsBackend.publicBuffer r.tls (← s.tlsRefs c) bytes
    tlsRecordLength := on "tls" fun c h => do TlsBackend.recordLength r.tls (← s.tlsRefs c) h
    tlsRevealRange := on "tls" fun c h o n => do TlsBackend.revealRange r.tls (← s.tlsRefs c) h o n
    contactsKey := on "contacts" fun id share => do
      let slot ← r.stashBits (share.map fun b => bitsOf (toB8 b))
      let _ ← tableStep r (fun t => Contacts.opKey t id slot) [slot]
    contactsLoad := on "contacts" fun id stored => do
      let (v, c, ct) := splitStored stored
      return Reveal.blobAccepted (← tableStep r fun t => Contacts.opOpen t id [0] v c ct).isSome
    contactsLoadDevices := on "contacts" fun id kinds body => do
      let (v, c, ct) := splitStored body
      return Reveal.blobAccepted (← tableStep r fun t => Contacts.opOpen t id kinds v c ct).isSome
    contactsSeal := on "contacts" fun id version => do
      let out := ofB8 (← tableStep r fun t => Contacts.opSeal t id (toB8 version))
      insist (out.length > 16) "invalid stored contact state"
      return Reveal.sealedBlob out
    contactsEvict := on "contacts" fun id => tableStep r fun t => Contacts.opEvict t id
    contactsAssign := on "contacts" fun p id => do
      return Reveal.assignStatus (← tableStep r fun t => Contacts.opAssign t p id)
    -- TEST (op 44, J23; `Flows/ContactsAdmit.lean`): the C++'s `need` on the account (admitted, its
    -- certificate in) and the record's size here; the table's own refusal (an id already present) in
    -- `opAdmit`. Party A's record bits are A's input (B's slot holds its own copy, unread).
    contactsAdmitTest := on "contacts" fun id record => do
      insist ((← get s.account).certificate.isSome && record.length == Contacts.recordBytes) "contact admission"
      let slot ← r.stashBits (record.map fun b => bitsOf (toB8 b))
      let _ ← tableStep r (fun t => Contacts.opAdmit t id slot) [slot]
    -- Op 91 (J22): the connection's script TLS state is replaced by a fresh one (the socket half is
    -- `Flow.Server.reset`'s, with the legacy library left alone: its phase never left `fresh`).
    serverReset := on "tls" fun c => do
      let i := c.getD 0
      let fresh ← (IO.mkRef {} : IO (IO.Ref (Tls.Conn JoinBackend.SplitState)))
      set s.conns ((i, fresh) :: (← get s.conns).filter (·.1 != i))
    accountKey := on "account" fun share => withCounters s fun a => do
      let slot ← r.stashBits (share.map fun b => bitsOf (toB8 b))
      let st := Account.keyStep a slot
      let h ← r.runReleasing st.1 [slot]
      return ((), st.2 h)
    accountSeal := on "account" fun version => withCounters s fun a => do
      let st := Account.sealStep a (toB8 version)
      let out := ofB8 (← r.run st.1)
      insist (out.length > 16) "invalid stored account state"
      return (Reveal.sealedBlob out, st.2)
    accountLoad := on "account" fun stored => do
      refill r 0 (if s.hinted then 503 else 252)
      let n ← r.allocB 19
      let f ← r.allocF 507
      let st ← Runner.get r.state
      let (v, c, ct) := splitStored stored
      let o ← r.run (Account.openStep (← get s.account) n f st.pool s.hinted v c ct)
      let st' ← Runner.get r.state
      Runner.set r.state { st' with pool := o.pool }
      set s.account { o.state with ctr := st'.table.ctr }
    accountCredentials := on "account" fun share => do
      insist (share.length == Account.credentialBytes) "account credentials"
      withCounters s fun a => do
        let slot ← r.stashBits (share.map fun b => bitsOf (toB8 b))
        let st := Account.credentialsStep a slot
        let p ← r.runReleasing st.1 [slot]
        return ((), st.2 p)
    accountAdmitTest := on "account" fun identity certificate => do
      insist (identity.length == 32 && !certificate.isEmpty && certificate.length ≤ 1024) "account admission"
      refill r 0 (if s.hinted then 503 else 252)
      let n ← r.allocB 19
      let f ← r.allocF 507
      let scalarSlot ← r.stashBits (identity.map fun b => bitsOf (toB8 b))
      let certSlot ← r.stashBits ((Secret.hide certificate).map fun b => bitsOf (toB8 b))
      let st ← Runner.get r.state
      let o ← r.runReleasing (Account.admitStep (← get s.account) n f st.pool s.hinted scalarSlot certSlot certificate.length)
        [scalarSlot, certSlot]
      let st' ← Runner.get r.state
      Runner.set r.state { st' with pool := o.pool }
      set s.account { o.state with ctr := st'.table.ctr }
    upgradeAuthenticated := on "account" fun c state => upgradeAuthenticated s c state
    curvePrepareContacts := on "curve" fun ids => do
      insist (!ids.isEmpty && ids.length ≤ 64) "prepare unavailable"
      for id in ids do
        let st ← Runner.get r.state
        if let some state := ContactsPrepare.needs st.table (← get s.prepared) id then
          prepareOne s id state
      let st ← Runner.get r.state
      let cache ← get s.prepared
      return Reveal.prepareStatus (ids.map fun id => UInt8.ofNat (ContactsPrepare.statusByte st.table cache id))
    ceremonySecrets := on "ceremony" (ceremonySecrets s)
    ceremonyRegister := on "ceremony" fun payloadAt offsets mask tail frame =>
      ceremonyRegister s payloadAt offsets mask tail frame
    sendSeal := on "send" fun id built => do SendBackend.seal r.tls sendCurve (← sendRefs none) id built
    sendSealDevices := on "send" fun id address built devices => do
      SendBackend.sealDevices r.tls sendCurve (← sendRefs none) id address built devices
    sendRequest := on "send" fun id offsets mask frame => do SendBackend.request r.tls (← sendRefs none) id offsets mask frame
    sendRequestDevices := on "send" fun id at_ offsets devices mask frame => do
      SendBackend.requestDevices r.tls (← sendRefs none) id at_ offsets devices mask frame
    tlsApplicationBackend := on "tls" fun c =>
      { sealApplication := fun keys sq payload size padding => do
          let refs ← s.tlsRefs c
          let sr ← sendRefs c
          if let some wire ← SendBackend.sealRequest r.tls sr payload.id sq size padding then
            return (Reveal.sealedRecord wire).val
          if let some wire ← RefreshBackend.sealFetch r (← refreshSources c) s.refresh payload.id sq size padding then
            return (Reveal.sealedRecord wire).val
          (TlsBackend.scriptApplicationBackend r.tls ka refs).sealApplication keys sq payload size padding
        sealControl := fun keys sq kind content => do
          (TlsBackend.scriptApplicationBackend r.tls ka (← s.tlsRefs c)).sealControl keys sq kind content
        openRecord := fun keys sq wire => do
          (TlsBackend.scriptApplicationBackend r.tls ka (← s.tlsRefs c)).openRecord keys sq wire
        rotateSend := fun keys => do (TlsBackend.scriptApplicationBackend r.tls ka (← s.tlsRefs c)).rotateSend keys
        rotateReceive := fun keys => do (TlsBackend.scriptApplicationBackend r.tls ka (← s.tlsRefs c)).rotateReceive keys
        abort := do (TlsBackend.scriptApplicationBackend r.tls ka (← s.tlsRefs c)).abort }
    receiveTake := on "receive" fun h o n => do (← receiveApi).take h o n
    receiveDrop := on "receive" (do (← receiveApi).drop)
    receiveOpenFirst := on "receive" fun ip now sk sc si => do (← receiveApi).openFirst ip now sk sc si
    receiveSession := on "receive" fun id address signed oneTime secret => do
      (← receiveApi).session id address signed oneTime secret
    refreshFetch := on "refresh" fun id at_ offsets mask frame => do
      (RefreshBackend.scriptApi r (← refreshSources none) s.refresh).fetch id at_ offsets mask frame
    refreshTake := on "refresh" fun h o n => do (RefreshBackend.scriptApi r (← refreshSources none) s.refresh).take h o n
    refreshDrop := on "refresh" (do (RefreshBackend.scriptApi r (← refreshSources none) s.refresh).drop)
    refreshShape := on "refresh" (do (RefreshBackend.scriptApi r (← refreshSources none) s.refresh).shape)
    refreshEstablish := on "refresh" fun id reg index devices step at_ slots widths => do
      refill r Join.agreeWords Join.checkBits
      (RefreshBackend.scriptApi r (← refreshSources none) s.refresh).establish id reg index devices step at_ slots widths
    refreshScratchSeal := on "refresh" fun id version => do
      (RefreshBackend.scriptApi r (← refreshSources none) s.refresh).scratchSeal id version
    refreshScratchCommit := on "refresh" fun id => do
      (RefreshBackend.scriptApi r (← refreshSources none) s.refresh).scratchCommit id }

end TlsMpc.Node.Flows.Select

namespace TlsMpc.Node.Flow
open TlsMpc.TlsWire

/-- **The flow context with the agreed selection** (`Flows/Select.lean`): as `Worker.start`, then,
when `agreed.scripts` names groups (accepted by `Select.check`, for this session's kind: `ceremony`,
the session is a registration ceremony, J22), one script runner for this party (`party`: 0 for A)
and the overrides of those groups. With no group it is `Worker.start`. -/
def Worker.startWith (pipe : TlsWorker.Rpc) (random : Nat → IO (Secret Bytes)) (party : Nat)
    (agreed : Config.Agreed) (ceremony : Bool) (loaded : Bytes → Bool) (programMasks : Bytes → Option Nat) :
    IO Worker := do
  let w ← Worker.start pipe random
  if agreed.scripts.isEmpty then return w
  match Flows.Select.check agreed.scripts ceremony with
  | .error e => throw (IO.userError e)
  | .ok () =>
    let r ← Flows.Runner.Runner.start w (if party = 0 then .a else .b) loaded programMasks
    let s ← Flows.Select.Session.start r agreed
    return { w with overrides := Flows.Select.overrides s agreed.scripts }

end TlsMpc.Node.Flow
