import TlsMpc.Node.Session.State

/-!
# The event abstraction of a session (REORGANIZATION_PLAN.md proof track P4: ORD-1, ORD-2, T11)

## The deployed functions are monad-generic definitions; what the theorems say about a real run

Since 2026-11-12 (PROOF_GAPS C3) every session function on the ORD-1 / ORD-2 / T11 paths is
defined ONCE, over any monad `m` with `[Monad m] [MonadExceptOf String m] [MonadStateOf State m]
[MonadReaderOf Context m]`, its effects being the fields of an operations record:

| definition | operations | deployed function (`abbrev`) |
|---|---|---|
| `State`: `modifyReportG`, `modifyPoolG`, `modifyContactsG`; `Common`: `appNowG` | none | `modifyReport`, … , `appNow` |
| `Store`: `kindsOfG` … `storeSoftG`, `commitScratchG` | `StoreOps` | `fG storeReal` |
| `Send`: `sendDevicesG`, `sendMessageG`, `sendSoftG` | `Send.SendOps` | `fG Send.sendReal` |
| `Send`: `refreshContactG`, `refreshSoftG` | `Send.RefreshOps` | `fG Send.refreshReal` |
| `Send`: `loopG` | `Send.LoopOps` | `Send.loop = loopG Send.loopReal` |
| `Send`: `deliverJobG` (tail `resultsTailG`) | `Send.DeliverOps` | `Send.deliverJob = deliverJobG Send.deliverReal` |
| `Serve`: `serveG` | `Serve.ServeOps` | `Serve.serve = serveG Serve.serveReal` |

The deployed function IS the definition at `SessionM` and the deployed record (`abbrev f := fG
realOps`; callers unchanged). There is no second copy of any text: the theorems in
`StoreProofs`, `SendProofs`, `DeliverProofs`, `LoopProofs`, `ServeProofs` are about these constants,
instantiated at a record of the model monad `Model` (below), and quantify over that record:
`storeModel E`, `sendModel E` for every environment `E`, and in the guarded theorems any record
`rest` / `R` / `D` of computations that keep the property, with the operations that matter (the
sends, `commitScratch`, the peer exchange) fixed to the definitions' own instances.

**What a theorem says about a real run.** A run of a deployed function is a run of the generic
definition at `SessionM` and the deployed record. The theorem says: at EVERY operations record of
`Model` whose calls are logged as modelled, every run of the same definition logs its events in the
stated order. The environment answers the i-th call (`World.calls`) of each operation as an arbitrary
function of the context, the call's arguments and `i` (black boxes: and the session state), so for a
given real run there is an environment that answers every call as that run's operation did; the
property holds of that environment's run, which performs the same calls in the same order with the
same answers. What carries this over to the real run, and is therefore still trusted:

1. **The real operations perform the effect their event names** ("logged as modelled"). For
   `Channels`: `writeAcknowledged name` returns `true` only when this party's database nodes
   acknowledged write `name` (event `acked`); `exchange` (`Common.peer`) sends our message and
   returns the other party's reply (`peer`); `db call` runs that client command (`db`). For `Flow`:
   `Send.seal` / `sealDevices` advance the contact's ratchet state in the engines (`seal c`);
   `Contacts.seal` seals the contact's CURRENT state for storage (`blobSeal c`); `Send.request` /
   `requestDevices` hand that contact's message request to the worker (`request c`), and nothing
   else does; `Refresh.scratchSeal` seals the scratch device list (`scratchSeal c`),
   `Refresh.scratchCommit` makes it the contact's state (`scratchCommit c`), `Refresh.drop` drops it
   (`scratchDrop`), and nothing else commits a scratch. These are the engines' and the worker's
   behaviour (A1, A2, A5 of PROOF_GAPS.md).
2. **What the model leaves to black boxes performs none of the logged effects that a property
   constrains**: no operation other than the records' `request` / `requestDevices` fields hands a
   message request to the worker, and none other than `scratchCommit` commits a scratch. In the
   code: `Flow.Send.request`, `Flow.Send.requestDevices` appear only in `Send.sendReal` and
   `Flow.Refresh.scratchCommit` only in `storeReal`; `scripts/lint_node.py` (rule `ordering-sites`)
   fails otherwise.
3. **The operations the model treats as atoms do not change the session `State`.** True of the
   deployed ones by their definitions: each is a `Flow.*` / `Channels` / `TlsApplication` action in
   `M` or `IO`, lifted into `SessionM` by `StateT.lift` (state unchanged), or `peer`, `dbTry`,
   `nonce`, which only read the context. `requestFile`, `recordSend` read the state (`rbox`);
   `restamp` changes it (`box`); the guarded theorems allow any change.
4. **Instantiation.** That the generic definition, run at `SessionM`, makes the calls its `Model`
   instance makes when every call is answered alike. Both are the same constant applied to two
   monad dictionaries; the definition uses nothing of the monad but `pure`, `bind`, `throw`,
   `tryCatch`, `get`/`set`/`modifyGet`, `read`, `Loop.forIn` and `List.forIn`, so this is the
   free theorem of its type. Lean does not state free theorems (and cannot observe `IO`); it is the
   one step that is argued, not proved, and it is about the compiler running the definition as
   written (A5), not about two texts agreeing: there is one text.

`while` loops (`Loop.forIn`, a `partial def`, opaque to proofs) are handled by the guarded monad
`Guarded` (below): a computation that carries a proof that it preserves an invariant of the log, so
whatever the loop does, its result preserves the invariant, by its type.

**The files.** `Events.lean` (this: events, model, automata, guarded monad); `StoreProofs.lean`
(the store before a send, ORD-2's commit, versions); `SendProofs.lean` (one send, ORD-1);
`DeliverProofs.lean` (`deliverJob`: ORD-1 over its loops, T11); `RefreshProofs.lean` (notes on the
refreshes); `LoopProofs.lean` (`loop`, and ORD-1/ORD-2 over `deliverJob` and `loop` with their
refreshes); `ServeProofs.lean` (`serve`: ORD-1/ORD-2).

## The abstraction

- `Event`: what a run does that ORD-1 / ORD-2 / T11 speak about (one constructor per kind of call);
- `World`: the number of environment calls so far and the event log, **newest first**;
- `Model`: `Context → State → World → Except String α × State × World`, the deployed monad's
  shape (failures keep the state: `ExceptT` over `StateT`) with `IO` replaced by `World`;
- `Model.atom`: an effect that does not touch `State` (a `Flow.*` call, a channel): its result is
  the environment's, and it logs the event the result determines;
- `Model.rbox` / `Model.box`: an effect that reads (and may change) `State` and logs nothing: the
  session functions treated as black boxes (`restamp`, `awaitSoft`, ...);
- `Model.wp`: weakest preconditions, the proof method;
- the phase automata `phase` (ORD-1, per contact) and `scratchPhase` (ORD-2), the log properties
  `SendsAcked`, `SendsAgreed`, `CommitsAgreed`;
- `Guarded I`: computations of `Model` that preserve `I` (for contexts with the database).

No I/O primitive; no emitter imports this module (nothing in the controller does: proofs only).
-/

/-! (Before 2026-11-12 the proof files held monad-generic *twins* of the session functions, proved
equal to the deployed definitions by `rfl` (`*_deployed`); the twins are now the definitions, and
those theorems are gone.) -/

namespace TlsMpc.Node.Session.Events
open TlsMpc TlsMpc.TlsWire TlsMpc.TlsClient TlsMpc.Node TlsMpc.Node.Session

/-! ### Events -/

/-- One event of a session run, as the abstraction sees it. -/
inductive Event where
  /-- `Flow.Send.seal` / `sealDevices` (ops 41, 61): a message to `contact` was sealed; the
  contact's ratchet state in the engines has advanced. -/
  | seal (contact : Nat)
  /-- `Flow.Contacts.seal` (op 38): the contact's current state sealed for storage. -/
  | blobSeal (contact : Nat)
  /-- `Flow.Refresh.scratchSeal` (op 64): a refresh's new device list sealed for storage. -/
  | scratchSeal (contact : Nat)
  /-- A database client call (`Channels.db`) and whether it succeeded. -/
  | db (call : DbCall) (ok : Bool)
  /-- `Channels.writeAcknowledged name`: whether this party's database nodes acknowledged write `name`. -/
  | acked (name : String) (yes : Bool)
  /-- `Channels.exchange` (`Common.peer`): our message to the other node and its reply (`none`: the
  exchange failed). -/
  | peer (sent : PeerMsg) (reply : Option PeerMsg)
  /-- `Flow.Send.request` / `requestDevices` (ops 42, 62): the request carrying the sealed message
  to `contact` handed to the worker. -/
  | request (contact : Nat)
  /-- `TlsApplication.send`: a request record handed to the TLS session to seal and send. -/
  | transmit (bytes : Nat)
  /-- `Flow.Refresh.scratchCommit` (op 65): the scratch device list became the contact's state. -/
  | scratchCommit (contact : Nat)
  /-- `Flow.Refresh.drop` (op 58): the scratch is dropped. -/
  | scratchDrop
  /-- Anything else that is logged (not used by the properties). -/
  | other (what : String)

/-- The other party's reply that its database nodes acknowledged too (`dbSubmitSoft`). -/
def Event.agrees : Event → Bool
  | .peer (.acknowledged true) (some (.acknowledged true)) => true
  | _ => false

/-! ### The model monad -/

/-- The environment calls so far and the event log (newest event first). -/
structure World where
  calls : Nat
  log : List Event

/-- The deployed monad's shape with `IO` replaced by `World`. -/
def Model (α : Type) : Type := Context → State → World → Except String α × State × World

namespace Model
variable {α β : Type}

@[inline] def pure' (a : α) : Model α := fun _ st w => (.ok a, st, w)

@[inline] def bind' (x : Model α) (f : α → Model β) : Model β := fun c st w =>
  match x c st w with
  | (.ok a, st', w') => f a c st' w'
  | (.error e, st', w') => (.error e, st', w')

instance : Monad Model where
  pure := pure'
  bind := bind'

instance : MonadExceptOf String Model where
  throw e := fun _ st w => (.error e, st, w)
  tryCatch x h := fun c st w =>
    match x c st w with
    | (.error e, st', w') => h e c st' w'
    | r => r

instance : MonadStateOf State Model where
  get := fun _ st w => (.ok st, st, w)
  set st' := fun _ _ w => (.ok (), st', w)
  modifyGet f := fun _ st w => ((.ok (f st).1), (f st).2, w)

instance : MonadReaderOf Context Model where
  read := fun c st w => (.ok c, st, w)

/-- An effect that does not touch the session state: the environment's answer `f c i` to the
`i`-th call, and the event `ev` of that answer prepended to the log. -/
@[inline] def atom (f : Context → Nat → Except String α) (ev : Except String α → Event) : Model α :=
  fun c st w => (f c w.calls, st, { calls := w.calls + 1, log := ev (f c w.calls) :: w.log })

/-- An effect that reads the session state and logs nothing (a black box). -/
@[inline] def rbox (f : Context → State → Nat → Except String α) : Model α :=
  fun c st w => (f c st w.calls, st, { w with calls := w.calls + 1 })

/-- An effect that may change the session state and logs nothing (a black box). -/
@[inline] def box (f : Context → State → Nat → Except String α × State) : Model α :=
  fun c st w => ((f c st w.calls).1, (f c st w.calls).2, { w with calls := w.calls + 1 })

/-- The event of a database call's outcome. -/
def okOf : Except String Bool → Bool
  | .ok b => b
  | .error _ => false

/-! #### Weakest preconditions: `wp x Q c st w` says that the run of `x` ends in `Q` -/

/-- The run of `x` in context `c` from `st`, `w` satisfies `Q` (its result, final state and world). -/
def wp (x : Model α) (Q : Except String α → State → World → Prop) (c : Context) (st : State) (w : World) : Prop :=
  Q (x c st w).1 (x c st w).2.1 (x c st w).2.2

theorem wp_iff (x : Model α) (Q : Except String α → State → World → Prop) (c st w) :
    wp x Q c st w ↔ Q (x c st w).1 (x c st w).2.1 (x c st w).2.2 := Iff.rfl

@[simp] theorem wp_pure (a : α) (Q : Except String α → State → World → Prop) (c st w) :
    wp (pure a) Q c st w = Q (.ok a) st w := rfl

@[simp] theorem wp_bind (x : Model α) (f : α → Model β) (Q : Except String β → State → World → Prop) (c st w) :
    wp (x >>= f) Q c st w = wp x (fun r st' w' => match r with
      | .ok a => wp (f a) Q c st' w'
      | .error e => Q (.error e) st' w') c st w := by
  unfold wp
  show Q (Model.bind' x f c st w).1 (Model.bind' x f c st w).2.1 (Model.bind' x f c st w).2.2 = _
  unfold Model.bind'
  rcases x c st w with ⟨r, st', w'⟩
  cases r <;> rfl

@[simp] theorem wp_throw (e : String) (Q : Except String α → State → World → Prop) (c st w) :
    wp (throw e : Model α) Q c st w = Q (.error e) st w := rfl
@[simp] theorem wp_throwThe (e : String) (Q : Except String α → State → World → Prop) (c st w) :
    wp (throwThe String e : Model α) Q c st w = Q (.error e) st w := rfl
@[simp] theorem wp_get (Q : Except String State → State → World → Prop) (c st w) :
    wp (get : Model State) Q c st w = Q (.ok st) st w := rfl
@[simp] theorem wp_getThe (Q : Except String State → State → World → Prop) (c st w) :
    wp (getThe State : Model State) Q c st w = Q (.ok st) st w := rfl
@[simp] theorem wp_modify (f : State → State) (Q : Except String Unit → State → World → Prop) (c st w) :
    wp (modify f : Model Unit) Q c st w = Q (.ok ()) (f st) w := rfl
@[simp] theorem wp_modifyGet (f : State → α × State) (Q : Except String α → State → World → Prop) (c st w) :
    wp (modifyGet f : Model α) Q c st w = Q (.ok (f st).1) (f st).2 w := rfl
@[simp] theorem wp_read (Q : Except String Context → State → World → Prop) (c st w) :
    wp (read : Model Context) Q c st w = Q (.ok c) st w := rfl
@[simp] theorem wp_readThe (Q : Except String Context → State → World → Prop) (c st w) :
    wp (readThe Context : Model Context) Q c st w = Q (.ok c) st w := rfl
@[simp] theorem wp_atom (f : Context → Nat → Except String α) (ev) (Q : Except String α → State → World → Prop) (c st w) :
    wp (atom f ev) Q c st w = Q (f c w.calls) st { calls := w.calls + 1, log := ev (f c w.calls) :: w.log } := rfl
@[simp] theorem wp_rbox (f : Context → State → Nat → Except String α) (Q : Except String α → State → World → Prop) (c st w) :
    wp (rbox f) Q c st w = Q (f c st w.calls) st { w with calls := w.calls + 1 } := rfl
@[simp] theorem wp_box (f : Context → State → Nat → Except String α × State) (Q : Except String α → State → World → Prop) (c st w) :
    wp (box f) Q c st w = Q (f c st w.calls).1 (f c st w.calls).2 { w with calls := w.calls + 1 } := rfl
@[simp] theorem wp_ite (p : Prop) [Decidable p] (x y : Model α) (Q : Except String α → State → World → Prop) (c st w) :
    wp (if p then x else y) Q c st w = if p then wp x Q c st w else wp y Q c st w := by
  split <;> rfl

/-- Weaken the postcondition. -/
theorem wp_mono {x : Model α} {Q Q' : Except String α → State → World → Prop} {c st w}
    (h : wp x Q c st w) (hq : ∀ r st' w', Q r st' w' → Q' r st' w') : wp x Q' c st w := hq _ _ _ h

/-- Two postconditions of the same run. -/
theorem wp_and {x : Model α} {Q₁ Q₂ : Except String α → State → World → Prop} {c st w}
    (h₁ : wp x Q₁ c st w) (h₂ : wp x Q₂ c st w) : wp x (fun r st' w' => Q₁ r st' w' ∧ Q₂ r st' w') c st w :=
  ⟨h₁, h₂⟩

/-- A postcondition that holds after every run, whatever `x` did, when the continuation
establishes it from every start: the shape of "after a loop (opaque), the tail decides". -/
theorem wp_bind_ok {x : Model α} {f : α → Model β} {Q : Except String β → State → World → Prop}
    (hf : ∀ a c st w, wp (f a) Q c st w) (herr : ∀ e st w, Q (.error e) st w) (c st w) :
    wp (x >>= f) Q c st w := by
  rw [wp_bind]
  unfold wp
  rcases x c st w with ⟨r, st', w'⟩
  cases r with
  | ok a => exact hf a c st' w'
  | error e => exact herr e st' w'

end Model

/-- One round of weakest-precondition rewriting (the `Model` lemmas above). -/
macro "wp_step" : tactic => `(tactic| simp only [Model.wp_bind, Model.wp_pure, Model.wp_atom, Model.wp_rbox,
  Model.wp_box, Model.wp_read, Model.wp_readThe, Model.wp_get, Model.wp_getThe, Model.wp_modify,
  Model.wp_modifyGet, Model.wp_throw, Model.wp_throwThe, Model.wp_ite])

/-! ### ORD-1: the per-contact phase of a message's state

Read newest first: `phase c log` is the phase after the events of `log`. The initial phase is
`sent` (the loaded state; nothing sealed since). -/

inductive Phase where
  /-- Nothing sealed since the last request (or since the state was loaded). -/
  | sent
  /-- A message was sealed (the ratchet advanced); its state is not stored. -/
  | sealed
  /-- The advanced state was sealed for storage after that. -/
  | stored
  /-- This party's nodes acknowledged it; the next event says whether the other party's did. -/
  | pending
  /-- Acknowledged by this party's nodes. -/
  | acked
  /-- Acknowledged by this party's nodes and reported acknowledged by the other party. -/
  | agreed
  deriving DecidableEq, Repr

/-- `pending` resolves to `acked` at any event that is not the other party's acknowledgement. -/
def Phase.settle : Phase → Phase
  | .pending => .acked
  | p => p

/-- Whether this party's nodes acknowledged the state (ORD-1, own acknowledgement). -/
def Phase.ownAck : Phase → Bool
  | .pending | .acked | .agreed => true
  | _ => false

/-- The step of contact `c`'s phase at one event (after `settle`). -/
def coreStep (c : Nat) (ph : Phase) : Event → Phase
  | .seal c' => if c' = c then .sealed else ph
  | .blobSeal c' => if c' = c ∧ ph = .sealed then .stored else ph
  | .acked n yes => if yes = true ∧ n = toString c ∧ ph = .stored then .pending else ph
  | .request c' => if c' = c then .sent else ph
  | _ => ph

def step (c : Nat) (ph : Phase) (e : Event) : Phase :=
  if ph = .pending ∧ e.agrees = true then .agreed else coreStep c ph.settle e

/-- Contact `c`'s phase after `log` (newest first). -/
def phase (c : Nat) : List Event → Phase
  | [] => .sent
  | e :: log => step c (phase c log) e

/-- **ORD-1 (own acknowledgement).** Every request to a contact is handed to the worker in a phase
where, after the last message sealed for it, its advanced state was sealed for storage and this
party's database nodes acknowledged that write; a request ends the phase (`sent`), so the next
request needs a new seal, a new storage seal and a new acknowledgement. -/
def SendsAcked : List Event → Prop
  | [] => True
  | e :: log => SendsAcked log ∧ ∀ c, e = .request c → (phase c log).ownAck = true

/-- **ORD-1 (both parties).** As `SendsAcked`, and the other party reported its nodes'
acknowledgement of the same write right after ours (the recovery path, `storeSoft`). -/
def SendsAgreed : List Event → Prop
  | [] => True
  | e :: log => SendsAgreed log ∧ ∀ c, e = .request c → phase c log = .agreed

/-! ### ORD-2: the per-contact phase of a refresh's scratch -/

inductive ScratchPhase where
  | idle
  | sealed
  | pending
  | acked
  | agreed
  deriving DecidableEq, Repr

def ScratchPhase.settle : ScratchPhase → ScratchPhase
  | .pending => .acked
  | p => p

def scratchCore (c : Nat) (sp : ScratchPhase) : Event → ScratchPhase
  | .scratchSeal c' => if c' = c then .sealed else sp
  | .acked n yes => if yes = true ∧ n = toString c ∧ sp = .sealed then .pending else sp
  | .scratchCommit c' => if c' = c then .idle else sp
  | .scratchDrop => .idle
  | _ => sp

def scratchStep (c : Nat) (sp : ScratchPhase) (e : Event) : ScratchPhase :=
  if sp = .pending ∧ e.agrees = true then .agreed else scratchCore c sp.settle e

def scratchPhase (c : Nat) : List Event → ScratchPhase
  | [] => .idle
  | e :: log => scratchStep c (scratchPhase c log) e

/-- **ORD-2.** A refresh's scratch becomes a contact's state (`scratchCommit`) only after it was
sealed for storage, this party's nodes acknowledged that write and the other party reported its
nodes' acknowledgement right after (and no drop or other commit in between). -/
def CommitsAgreed : List Event → Prop
  | [] => True
  | e :: log => CommitsAgreed log ∧ ∀ c, e = .scratchCommit c → scratchPhase c log = .agreed

/-! ### Lemmas on the automata -/

@[simp] theorem phase_nil (c : Nat) : phase c [] = .sent := rfl
@[simp] theorem phase_cons (c : Nat) (e : Event) (log : List Event) : phase c (e :: log) = step c (phase c log) e := rfl
@[simp] theorem scratchPhase_nil (c : Nat) : scratchPhase c [] = .idle := rfl
@[simp] theorem scratchPhase_cons (c : Nat) (e : Event) (log : List Event) :
    scratchPhase c (e :: log) = scratchStep c (scratchPhase c log) e := rfl
@[simp] theorem sendsAcked_nil : SendsAcked [] := trivial
@[simp] theorem sendsAcked_cons (e : Event) (log : List Event) :
    SendsAcked (e :: log) ↔ SendsAcked log ∧ ∀ c, e = .request c → (phase c log).ownAck = true := Iff.rfl
@[simp] theorem sendsAgreed_nil : SendsAgreed [] := trivial
@[simp] theorem sendsAgreed_cons (e : Event) (log : List Event) :
    SendsAgreed (e :: log) ↔ SendsAgreed log ∧ ∀ c, e = .request c → phase c log = .agreed := Iff.rfl
@[simp] theorem commitsAgreed_nil : CommitsAgreed [] := trivial
@[simp] theorem commitsAgreed_cons (e : Event) (log : List Event) :
    CommitsAgreed (e :: log) ↔ CommitsAgreed log ∧ ∀ c, e = .scratchCommit c → scratchPhase c log = .agreed := Iff.rfl

/-- Whether an event hands a message request to the worker (what ORD-1 constrains). -/
def Event.isRequest : Event → Bool
  | .request _ => true
  | _ => false

/-- Whether an event commits a scratch (what ORD-2 constrains). -/
def Event.isCommit : Event → Bool
  | .scratchCommit _ => true
  | _ => false

/-- `I` survives every event that is neither a request nor a commit. -/
def Stable (I : List Event → Prop) : Prop :=
  ∀ e l, e.isRequest = false → e.isCommit = false → I l → I (e :: l)

theorem stable_sendsAgreed : Stable SendsAgreed := fun e _ hr _ hl =>
  ⟨hl, fun c he => by subst he; simp [Event.isRequest] at hr⟩
theorem stable_sendsAcked : Stable SendsAcked := fun e _ hr _ hl =>
  ⟨hl, fun c he => by subst he; simp [Event.isRequest] at hr⟩
theorem stable_commitsAgreed : Stable CommitsAgreed := fun e _ _ hc hl =>
  ⟨hl, fun c he => by subst he; simp [Event.isCommit] at hc⟩

/-- A commit keeps the ORD-1 properties; a request keeps ORD-2's. -/
theorem sendsAgreed_commit (c : Nat) {l : List Event} (h : SendsAgreed l) : SendsAgreed (.scratchCommit c :: l) :=
  ⟨h, fun _ he => by cases he⟩
theorem sendsAcked_commit (c : Nat) {l : List Event} (h : SendsAcked l) : SendsAcked (.scratchCommit c :: l) :=
  ⟨h, fun _ he => by cases he⟩
theorem commitsAgreed_request (c : Nat) {l : List Event} (h : CommitsAgreed l) : CommitsAgreed (.request c :: l) :=
  ⟨h, fun _ he => by cases he⟩

theorem Stable.cons {I : List Event → Prop} (hI : Stable I) {e : Event} {l : List Event}
    (hr : e.isRequest = false) (hc : e.isCommit = false) (h : I l) : I (e :: l) := hI e l hr hc h

/-- Close `I (e₁ :: … :: l)` from `I l` and `hI : Stable I` when no `eᵢ` is a request or a commit. -/
macro "keep_log" hI:term : tactic => `(tactic| repeat (first | assumption |
  (refine Stable.cons $hI ?_ ?_ ?_ <;> try simp [Event.isRequest, Event.isCommit])))

/-- Both parties' acknowledgement implies our own. -/
theorem SendsAgreed.acked : ∀ {log : List Event}, SendsAgreed log → SendsAcked log
  | [], _ => trivial
  | _ :: _, ⟨h, hc⟩ => ⟨SendsAgreed.acked h, fun c he => by rw [hc c he]; rfl⟩

/-! ### Computations that preserve a log property (for contexts with the database nodes) -/

/-- `x` keeps `I` of the log, from every state, in every context with the database nodes (the
properties are about the database: without it nothing is stored before a send, by design: TEST). -/
def Preserves {α : Type} (I : List Event → Prop) (x : Model α) : Prop :=
  ∀ c st w, c.dbClient.isSome → I w.log → I (x c st w).2.2.log

/-- Computations of `Model` that preserve `I`. Every `Guarded` value preserves `I` by its type, so
whatever a `while` loop (`Loop.forIn`, opaque to proofs) does with guarded steps, the result
preserves `I`. -/
def Guarded (I : List Event → Prop) (α : Type) : Type := { x : Model α // Preserves I x }

namespace Guarded
variable {I : List Event → Prop} {α β : Type}

def pure' (a : α) : Guarded I α := ⟨pure a, fun _ _ _ _ h => h⟩

def bind' (x : Guarded I α) (f : α → Guarded I β) : Guarded I β :=
  ⟨x.1 >>= fun a => (f a).1, fun c st w hc h => by
    show I ((Model.bind' x.1 fun a => (f a).1) c st w).2.2.log
    unfold Model.bind'
    have hx := x.2 c st w hc h
    revert hx
    rcases x.1 c st w with ⟨r, st', w'⟩
    cases r with
    | ok a => exact fun hx => (f a).2 c st' w' hc hx
    | error e => exact fun hx => hx⟩

instance : Monad (Guarded I) where
  pure := pure'
  bind := bind'

instance : MonadExceptOf String (Guarded I) where
  throw e := ⟨throw e, fun _ _ _ _ h => h⟩
  tryCatch x handler := ⟨tryCatch x.1 (fun e => (handler e).1), fun c st w hc h => by
    show I ((match x.1 c st w with
      | (.error e, st', w') => (handler e).1 c st' w'
      | r => r)).2.2.log
    have hx := x.2 c st w hc h
    revert hx
    rcases x.1 c st w with ⟨r, st', w'⟩
    cases r with
    | ok a => exact fun hx => hx
    | error e => exact fun hx => (handler e).2 c st' w' hc hx⟩

instance : MonadStateOf State (Guarded I) where
  get := ⟨get, fun _ _ _ _ h => h⟩
  set st := ⟨set st, fun _ _ _ _ h => h⟩
  modifyGet f := ⟨modifyGet f, fun _ _ _ _ h => h⟩

instance : MonadReaderOf Context (Guarded I) where
  read := ⟨read, fun _ _ _ _ h => h⟩

/-- The model computation of a guarded bind is the model bind (the guard adds only the proof). -/
theorem bind_val (x : Guarded I α) (f : α → Guarded I β) : (x >>= f).1 = (x.1 >>= fun a => (f a).1) := rfl

/-- A logged effect whose every event keeps `I`. -/
def atom (f : Context → Nat → Except String α) (ev : Except String α → Event)
    (h : ∀ r l, I l → I (ev r :: l)) : Guarded I α :=
  ⟨Model.atom f ev, fun _ _ _ _ hl => h _ _ hl⟩

/-- A black box that logs nothing preserves every log property. -/
def box (f : Context → State → Nat → Except String α × State) : Guarded I α :=
  ⟨Model.box f, fun _ _ _ _ h => h⟩

def rbox (f : Context → State → Nat → Except String α) : Guarded I α :=
  ⟨Model.rbox f, fun _ _ _ _ h => h⟩

end Guarded

end TlsMpc.Node.Session.Events
