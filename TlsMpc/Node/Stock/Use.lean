import TlsMpc.Node.Stock.Journal
import TlsMpc.Node.Stock.Format

/-!
THE USE RULE OF THE STOCK, FOR ONE NODE AND FOR THE PAIR, AND T14 (STOCK USED ONCE).

X1 (PRODUCT_TODO.md 11a; REORGANIZATION_PLAN.md section 9 and T14 in 8.1). Pure: no I/O, no
escape hatch; no emitter imports this module.

WHAT IS AT STAKE. A stock item is the message-independent part of one two-party computation made
ahead of time: for the garbling node, a garbled circuit with its wire-label randomness; for the
evaluating node, the garbled tables and its precomputed oblivious-transfer correlations; in
malicious mode, authenticated triples and bits. Handing the same item to an engine twice breaks
security, and the damage falls on the node that reuses ITS OWN item:
  - the garbler that evaluates one garbled circuit on two inputs gives the evaluator two sets of
    active labels for the same circuit: the evaluator learns the XOR of the two input encodings
    and, through the shared gates, relations between the two runs' secrets (the garbler's inputs
    and intermediate values);
  - the evaluator that reuses its precomputed OT correlation sends the garbler c1 xor r and
    c2 xor r for two choice vectors: the garbler learns c1 xor c2, relations between the
    evaluator's inputs;
  - a reused authenticated triple (malicious mode) opens x - a and x' - a: the peer learns x - x'.
So each node must protect itself: the statements below are about ONE honest node and hold
whatever its peer does (lies about its index, replays, stops answering). The peer can only make
the honest node skip forward, which wastes items (availability), never reuse them.

THE NODE MODEL (`NodeState`, one shape; shapes have separate stocks, chains and journals, so
the statements hold per shape). Three kinds of memory, as in the deployment:
  - DISK (survives everything; may be copied and restored): the stock header (`Hdr`: the boot it
    was made in, the stock id), the number of items written (`size`), the consumed journal.
  - BOOT MEMORY (survives a process crash; lost at a reboot): the boot id and the stock's key
    (`Key`): the stock id, the USE CURSOR (the item keys below it are erased: the chain value at
    the cursor is all that is kept, and the chain only goes forward) and the PRODUCER CURSOR.
  - PROCESS MEMORY (lost at a crash): the phase of a take in progress.
A take is four steps, and a crash may come between any two: `start j` (check, append j to the
journal), `sync` (fsync), `decrypt` (derive item j's key from the chain at the use cursor, move
the cursor to j + 1, erasing the old chain values; decrypt), `hand` (give the item to the
engine). `skip j` moves forward without taking. The ghost field `handed` records every item
given to the engine, as (boot at that moment, stock id, index).

THE ADVERSARY. Every event of `Ev` may happen at any time, in any order, any number of times:
  - the PEER chooses the index of every round: `start j` is admitted for ANY j at or above the
    node's next index (the honest rule takes max(mine, peer's claim), `agreeIndex`, which is
    always such a j), so a lying peer is covered by quantifying over j;
  - `crash keep`: a process crash at any step, keeping any amount `keep` of the unsynced journal
    bytes (a torn record included), then the restart (Journal.lean);
  - `reboot keep`: a power loss or reboot: boot memory lost, a fresh boot id;
  - `restoreDisk i`: the disk replaced by any earlier copy of it (a snapshot, a backup);
  - `restoreBoot i`: boot memory rolled back to an earlier state of the same boot (for example a
    key holder whose state file is restored, or a VM memory snapshot without the disk);
  - lost messages are rounds that never start, or takes interrupted by a crash.

THE THEOREMS (T14 and friends). Three independent barriers, each sufficient on its own under
its own assumption, and their combination:
  - `T14_chain`: with the key chain, no item is handed twice in ANY trace without a boot-memory
    rollback (disk restores, crashes, reboots, lying peers included);
  - `T14_journal`: with the journal, no item is handed twice in any trace without a disk restore
    (boot-memory rollbacks included);
  - `T14`: in production (both), no item is handed twice in any trace that does not roll back
    BOTH the disk and boot memory of this node;
  - `full_rollback_reuse`, `journal_alone_disk_rollback`, `chain_alone_boot_rollback`,
    `no_barrier_reuse`: concrete traces showing each assumption is needed (a full snapshot of a
    node, disk and memory, restored, is outside what the node itself can see; the honest peer's
    claim then pushes the index forward, see STOCK.md);
  - `T14_boot`: an item is handed only during the boot in which its stock was made, in every
    trace (the boot id; `start_refused_other_boot`: a stock whose header carries another boot id
    is never started);
  - pair: `agreeIndex_*` (both honest nodes use max + 1; never back; no stock on either side means
    live preprocessing, never a refusal), and `waste_bound` (each interruption, a crash or a lost
    message on either node, wastes at most one item of each node).
-/

namespace TlsMpc.Node.Stock

open TlsMpc.Node.Engine

-- The case splits below apply one simp set to every case (`<;>`); in most cases some of its
-- arguments do not apply.
set_option linter.unusedSimpArgs false

/-! ## The node model -/

/-- Which barriers are switched on. Production: both. -/
structure Barriers where
  journal : Bool
  chain : Bool
  deriving DecidableEq, Repr

def production : Barriers := ⟨true, true⟩

/-- Boot memory's state of the stock: its id, the use cursor (keys below it are erased) and the
producer cursor (the next index to be written; keys below it were used to encrypt and erased). -/
structure Key where
  stock : Nat
  use : Nat
  prod : Nat
  deriving DecidableEq, Repr

/-- The disk: the header, how many items were written, the consumed journal. -/
structure Disk where
  hdr : Option Hdr := none
  size : Nat := 0
  journal : Journal := {}
  deriving DecidableEq, Repr

/-- The take in progress (process memory): boot, stock id, index. -/
inductive Phase where
  | idle
  | appended (b s j : Nat)
  | synced (b s j : Nat)
  | opened (b s j : Nat)
  deriving DecidableEq, Repr

structure NodeState where
  /-- boot memory -/
  boot : Nat := 0
  key : Option Key := none
  /-- disk -/
  disk : Disk := {}
  /-- process memory -/
  phase : Phase := .idle
  /-- ghost: stock ids are fresh (`stockCtr` is the next one); the stocks made, with the boot
  each was made in; the items handed to the engine; the copies the adversary may restore. -/
  stockCtr : Nat := 0
  stocks : List (Nat × Nat) := []
  handed : List (Nat × Nat × Nat) := []
  diskSnaps : List Disk := []
  bootSnaps : List (Option Key) := []
  deriving Repr

/-- Everything that can happen to one node. -/
inductive Ev where
  | start (j : Nat)
  | sync
  | decrypt
  | hand
  | skip (j : Nat)
  | crash (keep : Nat)
  | reboot (keep : Nat)
  | newStock
  | extend (k : Nat)
  | snapDisk
  | restoreDisk (i : Nat)
  | snapBoot
  | restoreBoot (i : Nat)
  deriving DecidableEq, Repr

inductive Refusal where
  | busy
  | unusable
  | behind
  | absent
  | erased
  | nothing
  | exhausted
  deriving DecidableEq, Repr

inductive Outcome where
  | ok
  | handed (j : Nat)
  | refused (r : Refusal)
  deriving DecidableEq, Repr

def cursor : Option Key → Nat
  | some k => k.use
  | none => 0

namespace NodeState

/-- The next index the node may use: one more than the journal's largest entry, and not below
the chain's use cursor. -/
def next (cfg : Barriers) (n : NodeState) : Nat :=
  max (if cfg.journal then n.disk.journal.next else 0) (if cfg.chain then cursor n.key else 0)

/-- The stock is usable when its header was made in this boot and boot memory holds its key. -/
def usable (n : NodeState) : Option Nat :=
  match n.disk.hdr, n.key with
  | some h, some k => if h.boot = n.boot ∧ h.id = k.stock then some k.stock else none
  | _, _ => none

/-- The key's stock and use cursor. -/
def sk (n : NodeState) : Option (Nat × Nat) := n.key.map (fun k => (k.stock, k.use))

end NodeState

def stepStart (cfg : Barriers) (n : NodeState) (j : Nat) : NodeState × Outcome :=
  match n.phase, n.usable with
  | .idle, some s =>
    if j < n.next cfg then (n, .refused .behind)
    else if n.disk.size ≤ j then (n, .refused .absent)
    else ({ n with disk := { n.disk with journal := n.disk.journal.append j },
                   phase := .appended n.boot s j }, .ok)
  | .idle, none => (n, .refused .unusable)
  | _, _ => (n, .refused .busy)

def stepSync (n : NodeState) : NodeState × Outcome :=
  match n.phase with
  | .appended b s j =>
    ({ n with disk := { n.disk with journal := n.disk.journal.sync }, phase := .synced b s j }, .ok)
  | _ => ({ n with disk := { n.disk with journal := n.disk.journal.sync } }, .ok)

def stepDecrypt (cfg : Barriers) (n : NodeState) : NodeState × Outcome :=
  match n.phase, n.key with
  | .synced b s j, some k =>
    if k.stock = s ∧ (cfg.chain = false ∨ k.use ≤ j) then
      ({ n with key := some { k with use := if cfg.chain then j + 1 else k.use },
                phase := .opened b s j }, .ok)
    else ({ n with phase := .idle }, .refused .erased)
  | .synced _ _ _, none => ({ n with phase := .idle }, .refused .erased)
  | _, _ => (n, .refused .nothing)

def stepHand (n : NodeState) : NodeState × Outcome :=
  match n.phase with
  | .opened _ s j => ({ n with phase := .idle, handed := n.handed ++ [(n.boot, s, j)] }, .handed j)
  | _ => (n, .refused .nothing)

def stepSkip (cfg : Barriers) (n : NodeState) (j : Nat) : NodeState × Outcome :=
  match n.phase, n.usable with
  | .idle, some _ =>
    if j ≤ n.next cfg then (n, .ok)
    else ({ n with disk := { n.disk with journal := (n.disk.journal.append (j - 1)).sync },
                   key := n.key.map (fun k => if cfg.chain then { k with use := j } else k) }, .ok)
  | .idle, none => (n, .refused .unusable)
  | _, _ => (n, .refused .busy)

def stepCrash (n : NodeState) (keep : Nat) : NodeState × Outcome :=
  ({ n with disk := { n.disk with journal := n.disk.journal.crash keep }, phase := .idle }, .ok)

def stepReboot (n : NodeState) (keep : Nat) : NodeState × Outcome :=
  ({ n with boot := n.boot + 1, key := none, bootSnaps := [],
            disk := { n.disk with journal := n.disk.journal.crash keep }, phase := .idle }, .ok)

def stepNewStock (n : NodeState) : NodeState × Outcome :=
  match n.phase with
  | .idle =>
    ({ n with stockCtr := n.stockCtr + 1, stocks := (n.stockCtr, n.boot) :: n.stocks,
              key := some ⟨n.stockCtr, 0, 0⟩,
              disk := { hdr := some ⟨n.boot, n.stockCtr⟩, size := 0, journal := {} } }, .ok)
  | _ => (n, .refused .busy)

def stepExtend (cfg : Barriers) (n : NodeState) (k : Nat) : NodeState × Outcome :=
  match n.usable, n.key with
  | some _, some key =>
    if n.next cfg ≤ n.disk.size ∧ key.prod = n.disk.size then
      ({ n with disk := { n.disk with size := n.disk.size + k },
                key := some { key with prod := key.prod + k } }, .ok)
    else (n, .refused .exhausted)
  | _, _ => (n, .refused .unusable)

def stepRestoreDisk (n : NodeState) (i : Nat) : NodeState × Outcome :=
  match n.diskSnaps[i]? with
  | some d => ({ n with disk := d, phase := .idle }, .ok)
  | none => (n, .refused .nothing)

def stepRestoreBoot (n : NodeState) (i : Nat) : NodeState × Outcome :=
  match n.bootSnaps[i]? with
  | some k => ({ n with key := k, phase := .idle }, .ok)
  | none => (n, .refused .nothing)

/-- One event. -/
def step (cfg : Barriers) (n : NodeState) : Ev → NodeState × Outcome
  | .start j => stepStart cfg n j
  | .sync => stepSync n
  | .decrypt => stepDecrypt cfg n
  | .hand => stepHand n
  | .skip j => stepSkip cfg n j
  | .crash keep => stepCrash n keep
  | .reboot keep => stepReboot n keep
  | .newStock => stepNewStock n
  | .extend k => stepExtend cfg n k
  | .snapDisk => ({ n with diskSnaps := n.diskSnaps ++ [n.disk] }, .ok)
  | .restoreDisk i => stepRestoreDisk n i
  | .snapBoot => ({ n with bootSnaps := n.bootSnaps ++ [n.key] }, .ok)
  | .restoreBoot i => stepRestoreBoot n i

/-- A trace. -/
def run (cfg : Barriers) (n : NodeState) : List Ev → NodeState
  | [] => n
  | e :: es => run cfg (step cfg n e).1 es

/-- The node before anything happened. -/
def init : NodeState := {}

theorem run_preserves (cfg : Barriers) (P : NodeState → Prop) (A : Ev → Prop)
    (h : ∀ n e, A e → P n → P (step cfg n e).1) :
    ∀ (evs : List Ev) (n : NodeState), (∀ e ∈ evs, A e) → P n → P (run cfg n evs)
  | [], _, _, hn => hn
  | e :: es, n, ha, hn =>
    run_preserves cfg P A h es _ (fun x hx => ha x (List.mem_cons_of_mem e hx)) (h n e (ha e List.mem_cons_self) hn)

theorem usable_some {n : NodeState} {s : Nat} (h : n.usable = some s) :
    ∃ hd k, n.disk.hdr = some hd ∧ n.key = some k ∧ hd.boot = n.boot ∧ hd.id = s ∧ k.stock = s := by
  unfold NodeState.usable at h
  cases hh : n.disk.hdr with
  | none => simp [hh] at h
  | some hd =>
    cases hk : n.key with
    | none => simp [hh, hk] at h
    | some k =>
      simp only [hh, hk] at h
      by_cases hc : hd.boot = n.boot ∧ hd.id = k.stock
      · rw [if_pos hc] at h
        simp only [Option.some.injEq] at h
        exact ⟨hd, k, rfl, rfl, hc.1, hc.2.trans h, h⟩
      · rw [if_neg hc] at h
        simp at h

theorem journal_le_next {cfg : Barriers} (hj : cfg.journal = true) (n : NodeState) :
    n.disk.journal.next ≤ n.next cfg := by
  simp only [NodeState.next, hj, if_true]
  exact Nat.le_max_left _ _

theorem cursor_le_next {cfg : Barriers} (hc : cfg.chain = true) (n : NodeState) :
    cursor n.key ≤ n.next cfg := by
  simp only [NodeState.next, hc, if_true]
  exact Nat.le_max_right _ _

/-! ## The chain barrier -/

/-- The invariant of the key chain. -/
structure ChainInv (n : NodeState) : Prop where
  nodup : n.handed.Nodup
  below : ∀ b s j, (b, s, j) ∈ n.handed → ∀ c, n.sk = some (s, c) → j < c
  oldStock : ∀ b s j, (b, s, j) ∈ n.handed → s < n.stockCtr
  keyStock : ∀ s c, n.sk = some (s, c) → s < n.stockCtr
  opened : ∀ b s j, n.phase = .opened b s j →
    n.sk = some (s, j + 1) ∧ ∀ b' j', (b', s, j') ∈ n.handed → j' < j

theorem ChainInv.frame {n n' : NodeState} (h : ChainInv n) (hh : n'.handed = n.handed)
    (hk : n'.sk = n.sk) (hc : n'.stockCtr = n.stockCtr)
    (hp : ∀ b s j, n'.phase = .opened b s j → n.phase = .opened b s j) : ChainInv n' where
  nodup := hh ▸ h.nodup
  below := by
    intro b s j hm c hs
    rw [hh] at hm; rw [hk] at hs
    exact h.below b s j hm c hs
  oldStock := by
    intro b s j hm
    rw [hh] at hm; rw [hc]
    exact h.oldStock b s j hm
  keyStock := by
    intro s c hs
    rw [hk] at hs; rw [hc]
    exact h.keyStock s c hs
  opened := by
    intro b s j hph
    rw [hk, hh]
    exact h.opened b s j (hp b s j hph)

theorem chain_start (cfg : Barriers) (n : NodeState) (j : Nat) (h : ChainInv n) :
    ChainInv (stepStart cfg n j).1 := by
  unfold stepStart
  cases hp : n.phase <;> cases hu : n.usable <;> simp only [hp, hu] <;> try exact h
  split
  · exact h
  · split
    · exact h
    · exact h.frame rfl rfl rfl (by intro _ _ _ hph; simp at hph)

theorem chain_sync (n : NodeState) (h : ChainInv n) : ChainInv (stepSync n).1 := by
  unfold stepSync
  cases hp : n.phase
  all_goals
    simp only [hp]
    exact h.frame rfl rfl rfl (by intro _ _ _ hph; simp_all)

theorem chain_decrypt (cfg : Barriers) (hc : cfg.chain = true) (n : NodeState) (h : ChainInv n) :
    ChainInv (stepDecrypt cfg n).1 := by
  unfold stepDecrypt
  cases hp : n.phase <;> cases hk : n.key <;> simp only [hp, hk] <;> try exact h
  case synced.none b s j =>
    exact h.frame rfl (by simp [NodeState.sk, hk]) rfl (by intro _ _ _ hph; simp at hph)
  case synced.some b s j k =>
    split
    · rename_i hcond
      obtain ⟨hks, hu⟩ := hcond
      have hu' : k.use ≤ j := by
        rcases hu with hu | hu
        · rw [hc] at hu; exact absurd hu (by decide)
        · exact hu
      have hsk : n.sk = some (s, k.use) := by simp [NodeState.sk, hk, hks]
      refine ⟨h.nodup, ?_, h.oldStock, ?_, ?_⟩
      · intro b' s' j' hm c hs
        simp only [NodeState.sk, hc, if_true, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨hs1, hs2⟩ := hs
        have := h.below b' s' j' hm k.use (by rw [hsk, ← hs1, hks])
        omega
      · intro s' c hs
        simp only [NodeState.sk, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
        exact h.keyStock s' k.use (by rw [hsk, ← hs.1, hks])
      · intro b' s' j' hph
        simp only [Phase.opened.injEq] at hph
        obtain ⟨rfl, rfl, rfl⟩ := hph
        refine ⟨by simp [NodeState.sk, hc, hks], ?_⟩
        intro b'' j'' hm
        have := h.below b'' s j'' hm k.use hsk
        omega
    · exact h.frame rfl (by simp [NodeState.sk, hk]) rfl (by intro _ _ _ hph; simp at hph)

theorem chain_hand (n : NodeState) (h : ChainInv n) : ChainInv (stepHand n).1 := by
  unfold stepHand
  cases hp : n.phase <;> simp only [hp] <;> try exact h
  case opened b s j =>
    obtain ⟨hsk, hlt⟩ := h.opened b s j hp
    refine ⟨?_, ?_, ?_, h.keyStock, ?_⟩
    · rw [List.nodup_append]
      refine ⟨h.nodup, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, ?_⟩
      intro a ha x hx heq
      simp only [List.mem_singleton] at hx
      subst hx; subst heq
      have := hlt n.boot j ha
      omega
    · intro b' s' j' hm c hs
      rw [List.mem_append] at hm
      rcases hm with hm | hm
      · exact h.below b' s' j' hm c hs
      · simp only [List.mem_singleton, Prod.mk.injEq] at hm
        obtain ⟨_, rfl, rfl⟩ := hm
        have hs' : n.sk = some (s', c) := hs
        rw [hsk] at hs'
        simp only [Option.some.injEq, Prod.mk.injEq] at hs'
        omega
    · intro b' s' j' hm
      rw [List.mem_append] at hm
      rcases hm with hm | hm
      · exact h.oldStock _ _ _ hm
      · simp only [List.mem_singleton, Prod.mk.injEq] at hm
        obtain ⟨_, rfl, rfl⟩ := hm
        exact h.keyStock _ _ hsk
    · intro _ _ _ hph
      simp at hph

theorem chain_skip (cfg : Barriers) (hc : cfg.chain = true) (n : NodeState) (j : Nat) (h : ChainInv n) :
    ChainInv (stepSkip cfg n j).1 := by
  unfold stepSkip
  cases hp : n.phase <;> cases hu : n.usable <;> simp only [hp, hu] <;> try exact h
  split
  · exact h
  · rename_i hlt
    have hcur := cursor_le_next hc n
    refine ⟨h.nodup, ?_, h.oldStock, ?_, ?_⟩
    · intro b s j' hm c hs
      cases hk : n.key with
      | none => simp [NodeState.sk, hk] at hs
      | some k =>
        simp only [NodeState.sk, hk, hc, if_true, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨hs1, hs2⟩ := hs
        have := h.below b s j' hm k.use (by simp [NodeState.sk, hk, hs1])
        simp only [cursor, hk] at hcur
        omega
    · intro s c hs
      cases hk : n.key with
      | none => simp [NodeState.sk, hk] at hs
      | some k =>
        simp only [NodeState.sk, hk, hc, if_true, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
        exact h.keyStock s k.use (by simp [NodeState.sk, hk, hs.1])
    · intro _ _ _ hph
      simp at hph

theorem chain_crash (n : NodeState) (keep : Nat) (h : ChainInv n) : ChainInv (stepCrash n keep).1 :=
  h.frame rfl rfl rfl (by intro _ _ _ hph; simp [stepCrash] at hph)

theorem chain_reboot (n : NodeState) (keep : Nat) (h : ChainInv n) : ChainInv (stepReboot n keep).1 where
  nodup := h.nodup
  below := by intro _ _ _ _ _ hs; simp [stepReboot, NodeState.sk] at hs
  oldStock := h.oldStock
  keyStock := by intro _ _ hs; simp [stepReboot, NodeState.sk] at hs
  opened := by intro _ _ _ hph; simp [stepReboot] at hph

theorem chain_newStock (n : NodeState) (h : ChainInv n) : ChainInv (stepNewStock n).1 := by
  unfold stepNewStock
  cases hp : n.phase <;> simp only [hp] <;> try exact h
  refine ⟨h.nodup, ?_, ?_, ?_, ?_⟩
  · intro b s j hm c hs
    simp only [NodeState.sk, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
    have := h.oldStock b s j hm
    omega
  · intro b s j hm
    have := h.oldStock b s j hm
    simp only
    omega
  · intro s c hs
    simp only [NodeState.sk, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
    simp only
    omega
  · intro _ _ _ hph
    simp at hph

theorem chain_extend (cfg : Barriers) (n : NodeState) (k : Nat) (h : ChainInv n) :
    ChainInv (stepExtend cfg n k).1 := by
  unfold stepExtend
  cases hu : n.usable <;> cases hk : n.key <;> simp only [hu, hk] <;> try exact h
  split
  · exact h.frame rfl (by simp [NodeState.sk, hk]) rfl (by intro _ _ _ hph; exact hph)
  · exact h

theorem chain_restoreDisk (n : NodeState) (i : Nat) (h : ChainInv n) : ChainInv (stepRestoreDisk n i).1 := by
  unfold stepRestoreDisk
  cases hd : n.diskSnaps[i]? <;> simp only [hd]
  · exact h
  · exact h.frame rfl rfl rfl (by intro _ _ _ hph; simp at hph)

/-- Every event but a boot-memory rollback keeps the chain invariant. -/
theorem chain_step (cfg : Barriers) (hc : cfg.chain = true) (n : NodeState) (e : Ev)
    (he : ∀ i, e ≠ .restoreBoot i) (h : ChainInv n) : ChainInv (step cfg n e).1 := by
  cases e with
  | start j => exact chain_start cfg n j h
  | sync => exact chain_sync n h
  | decrypt => exact chain_decrypt cfg hc n h
  | hand => exact chain_hand n h
  | skip j => exact chain_skip cfg hc n j h
  | crash keep => exact chain_crash n keep h
  | reboot keep => exact chain_reboot n keep h
  | newStock => exact chain_newStock n h
  | extend k => exact chain_extend cfg n k h
  | snapDisk => exact h.frame rfl rfl rfl (fun _ _ _ hph => hph)
  | restoreDisk i => exact chain_restoreDisk n i h
  | snapBoot => exact h.frame rfl rfl rfl (fun _ _ _ hph => hph)
  | restoreBoot i => exact absurd rfl (he i)

theorem chainInv_init : ChainInv init where
  nodup := List.nodup_nil
  below := by intro _ _ _ hm; simp [init] at hm
  oldStock := by intro _ _ _ hm; simp [init] at hm
  keyStock := by intro _ _ hs; simp [init, NodeState.sk] at hs
  opened := by intro _ _ _ hph; simp [init] at hph

/-- **T14, chain barrier.** With the key chain, in every trace without a rollback of boot memory
(any crashes, reboots, disk restores, any indices chosen by the peer), no item is handed to the
engine twice. -/
theorem T14_chain (cfg : Barriers) (hc : cfg.chain = true) (evs : List Ev)
    (h : ∀ i, Ev.restoreBoot i ∉ evs) : (run cfg init evs).handed.Nodup :=
  (run_preserves cfg ChainInv (fun e => ∀ i, e ≠ .restoreBoot i)
    (fun n e he hn => chain_step cfg hc n e he hn) evs init
    (fun _ he i hei => h i (hei ▸ he)) chainInv_init).nodup

/-! ## The journal barrier -/

/-- The invariant of the consumed journal. -/
structure JournalInv (n : NodeState) : Prop where
  nodup : n.handed.Nodup
  below : ∀ b s j, (b, s, j) ∈ n.handed → ∀ hd, n.disk.hdr = some hd → hd.id = s →
    j < n.disk.journal.durableNext
  oldStock : ∀ b s j, (b, s, j) ∈ n.handed → s < n.stockCtr
  hdrStock : ∀ hd, n.disk.hdr = some hd → hd.id < n.stockCtr
  wf : n.disk.journal.synced ≤ n.disk.journal.entries.length
  inflight : ∀ b s j, (n.phase = .appended b s j ∨ n.phase = .synced b s j ∨ n.phase = .opened b s j) →
    (∃ hd, n.disk.hdr = some hd ∧ hd.id = s) ∧ j ∈ n.disk.journal.entries ∧
      ∀ b' j', (b', s, j') ∈ n.handed → j' < j
  durable : ∀ b s j, (n.phase = .synced b s j ∨ n.phase = .opened b s j) → j ∈ n.disk.journal.durable

theorem JournalInv.frame {n n' : NodeState} (h : JournalInv n) (hh : n'.handed = n.handed)
    (hc : n'.stockCtr = n.stockCtr) (hd : n'.disk.hdr = n.disk.hdr) (hj : n'.disk.journal = n.disk.journal)
    (hp : n'.phase = n.phase ∨ n'.phase = .idle) : JournalInv n' where
  nodup := hh ▸ h.nodup
  below := by
    intro b s j hm hd' hh' hs
    rw [hh] at hm; rw [hd] at hh'; rw [hj]
    exact h.below b s j hm hd' hh' hs
  oldStock := by
    intro b s j hm
    rw [hh] at hm; rw [hc]
    exact h.oldStock b s j hm
  hdrStock := by
    intro hd' hh'
    rw [hd] at hh'; rw [hc]
    exact h.hdrStock hd' hh'
  wf := by rw [hj]; exact h.wf
  inflight := by
    intro b s j hph
    rcases hp with hp | hp
    · rw [hp] at hph; rw [hd, hj, hh]; exact h.inflight b s j hph
    · rw [hp] at hph; simp at hph
  durable := by
    intro b s j hph
    rcases hp with hp | hp
    · rw [hp] at hph; rw [hj]; exact h.durable b s j hph
    · rw [hp] at hph; simp at hph

theorem journal_start (cfg : Barriers) (hjc : cfg.journal = true) (n : NodeState) (j : Nat)
    (h : JournalInv n) : JournalInv (stepStart cfg n j).1 := by
  unfold stepStart
  cases hp : n.phase <;> cases hu : n.usable <;> simp only [hp, hu] <;> try exact h
  rename_i s
  split
  · exact h
  · split
    · exact h
    · rename_i hnb _
      obtain ⟨hd, k, hhd, hk, hboot, hid, hks⟩ := usable_some hu
      have hnext := journal_le_next hjc n
      have hdn := Journal.durableNext_le_next n.disk.journal
      have happ : (n.disk.journal.append j).durableNext = n.disk.journal.durableNext := by
        simp only [Journal.durableNext, Journal.durable_append _ h.wf]
      refine ⟨h.nodup, ?_, h.oldStock, h.hdrStock, ?_, ?_, ?_⟩
      · intro b s' j' hm hd' hh' hs
        simp only at hh' ⊢
        rw [happ]
        exact h.below b s' j' hm hd' hh' hs
      · simp only [Journal.append, List.length_append]
        have := h.wf
        omega
      · intro b s' j' hph
        simp only [Phase.appended.injEq, reduceCtorEq, false_and, or_false] at hph
        obtain ⟨rfl, rfl, rfl⟩ := hph
        refine ⟨⟨hd, hhd, hid⟩, by simp [Journal.append], ?_⟩
        intro b' j'' hm
        have := h.below b' s j'' hm hd hhd hid
        omega
      · intro _ _ _ hph
        simp at hph

theorem journal_sync (n : NodeState) (h : JournalInv n) : JournalInv (stepSync n).1 := by
  have hdn : n.disk.journal.durableNext ≤ n.disk.journal.sync.durableNext := by
    simp only [Journal.durableNext, Journal.durable_sync]
    exact Journal.durableNext_le_next n.disk.journal
  have hwf : n.disk.journal.sync.synced ≤ n.disk.journal.sync.entries.length := by
    simp [Journal.sync]
  have hmem : ∀ b s j, (n.phase = .appended b s j ∨ n.phase = .synced b s j ∨ n.phase = .opened b s j) →
      j ∈ n.disk.journal.sync.durable := by
    intro b s j hph
    rw [Journal.durable_sync]
    exact (h.inflight b s j hph).2.1
  unfold stepSync
  split
  next b s j hp =>
    refine ⟨h.nodup, ?_, h.oldStock, h.hdrStock, hwf, ?_, ?_⟩
    · intro b' s' j' hm hd' hh' hs
      exact Nat.lt_of_lt_of_le (h.below b' s' j' hm hd' hh' hs) hdn
    · intro b' s' j' hph
      simp only [reduceCtorEq, Phase.synced.injEq, false_or, or_false] at hph
      obtain ⟨rfl, rfl, rfl⟩ := hph
      exact h.inflight b s j (Or.inl hp)
    · intro b' s' j' hph
      simp only [Phase.synced.injEq, reduceCtorEq, or_false] at hph
      obtain ⟨rfl, rfl, rfl⟩ := hph
      exact hmem b s j (Or.inl hp)
  next =>
    refine ⟨h.nodup, ?_, h.oldStock, h.hdrStock, hwf, ?_, ?_⟩
    · intro b' s' j' hm hd' hh' hs
      exact Nat.lt_of_lt_of_le (h.below b' s' j' hm hd' hh' hs) hdn
    · intro b' s' j' hph
      exact h.inflight b' s' j' hph
    · intro b' s' j' hph
      exact hmem b' s' j' (Or.inr hph)

theorem journal_decrypt (cfg : Barriers) (n : NodeState) (h : JournalInv n) :
    JournalInv (stepDecrypt cfg n).1 := by
  unfold stepDecrypt
  cases hp : n.phase <;> cases hk : n.key <;> simp only [hp, hk] <;> try exact h
  case synced.none b s j =>
    exact h.frame rfl rfl rfl rfl (Or.inr rfl)
  case synced.some b s j k =>
    split
    · refine ⟨h.nodup, h.below, h.oldStock, h.hdrStock, h.wf, ?_, ?_⟩
      · intro b' s' j' hph
        simp only [reduceCtorEq, Phase.opened.injEq, false_or] at hph
        obtain ⟨rfl, rfl, rfl⟩ := hph
        exact h.inflight b s j (Or.inr (Or.inl hp))
      · intro b' s' j' hph
        simp only [reduceCtorEq, Phase.opened.injEq, false_or] at hph
        obtain ⟨rfl, rfl, rfl⟩ := hph
        exact h.durable b s j (Or.inl hp)
    · exact h.frame rfl rfl rfl rfl (Or.inr rfl)

theorem journal_hand (n : NodeState) (h : JournalInv n) : JournalInv (stepHand n).1 := by
  unfold stepHand
  cases hp : n.phase <;> simp only [hp] <;> try exact h
  case opened b s j =>
    obtain ⟨⟨hd, hhd, hid⟩, _, hlt⟩ := h.inflight b s j (Or.inr (Or.inr hp))
    have hdur := h.durable b s j (Or.inr hp)
    refine ⟨?_, ?_, ?_, h.hdrStock, h.wf, ?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨h.nodup, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, ?_⟩
      intro a ha x hx heq
      simp only [List.mem_singleton] at hx
      subst hx; subst heq
      have := hlt n.boot j ha
      omega
    · intro b' s' j' hm hd' hh' hs
      rw [List.mem_append] at hm
      rcases hm with hm | hm
      · exact h.below b' s' j' hm hd' hh' hs
      · simp only [List.mem_singleton, Prod.mk.injEq] at hm
        obtain ⟨_, rfl, rfl⟩ := hm
        exact lt_nextOf_of_mem hdur
    · intro b' s' j' hm
      rw [List.mem_append] at hm
      rcases hm with hm | hm
      · exact h.oldStock _ _ _ hm
      · simp only [List.mem_singleton, Prod.mk.injEq] at hm
        obtain ⟨_, rfl, rfl⟩ := hm
        rw [← hid]
        exact h.hdrStock hd hhd
    · intro _ _ _ hph
      simp at hph
    · intro _ _ _ hph
      simp at hph

theorem journal_skip (cfg : Barriers) (n : NodeState) (j : Nat) (h : JournalInv n) :
    JournalInv (stepSkip cfg n j).1 := by
  unfold stepSkip
  cases hp : n.phase <;> cases hu : n.usable <;> simp only [hp, hu] <;> try exact h
  split
  · exact h
  · have hdn : n.disk.journal.durableNext ≤ ((n.disk.journal.append (j - 1)).sync).durableNext := by
      simp only [Journal.durableNext, Journal.durable_sync, Journal.append]
      exact nextOf_mono (fun e he => List.mem_append_left _ (List.mem_of_mem_take he))
    refine ⟨h.nodup, ?_, h.oldStock, h.hdrStock, ?_, ?_, ?_⟩
    · intro b' s' j' hm hd' hh' hs
      exact Nat.lt_of_lt_of_le (h.below b' s' j' hm hd' hh' hs) hdn
    · simp [Journal.sync]
    · intro _ _ _ hph
      simp at hph
    · intro _ _ _ hph
      simp at hph

theorem crash_durableNext (j : Journal) (keep : Nat) : (j.crash keep).durableNext = (j.crash keep).next := by
  simp only [Journal.durableNext, Journal.durable, Journal.next, Journal.crash, List.take_length]

theorem journal_crash (n : NodeState) (keep : Nat) (h : JournalInv n) : JournalInv (stepCrash n keep).1 where
  nodup := h.nodup
  below := by
    intro b s j hm hd hh hs
    simp only [stepCrash] at hh ⊢
    rw [crash_durableNext]
    exact Nat.lt_of_lt_of_le (h.below b s j hm hd hh hs) (Journal.durableNext_le_crash _ _)
  oldStock := h.oldStock
  hdrStock := h.hdrStock
  wf := by simp [stepCrash, Journal.crash]
  inflight := by intro _ _ _ hph; simp [stepCrash] at hph
  durable := by intro _ _ _ hph; simp [stepCrash] at hph

theorem journal_reboot (n : NodeState) (keep : Nat) (h : JournalInv n) : JournalInv (stepReboot n keep).1 where
  nodup := h.nodup
  below := by
    intro b s j hm hd hh hs
    simp only [stepReboot] at hh ⊢
    rw [crash_durableNext]
    exact Nat.lt_of_lt_of_le (h.below b s j hm hd hh hs) (Journal.durableNext_le_crash _ _)
  oldStock := h.oldStock
  hdrStock := h.hdrStock
  wf := by simp [stepReboot, Journal.crash]
  inflight := by intro _ _ _ hph; simp [stepReboot] at hph
  durable := by intro _ _ _ hph; simp [stepReboot] at hph

theorem journal_newStock (n : NodeState) (h : JournalInv n) : JournalInv (stepNewStock n).1 := by
  unfold stepNewStock
  cases hp : n.phase <;> simp only [hp] <;> try exact h
  refine ⟨h.nodup, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b s j hm hd hh hs
    simp only [Option.some.injEq] at hh
    subst hh
    have := h.oldStock b s j hm
    simp only at hs
    omega
  · intro b s j hm
    have := h.oldStock b s j hm
    simp only
    omega
  · intro hd hh
    simp only [Option.some.injEq] at hh
    subst hh
    simp only
    omega
  · simp
  · intro _ _ _ hph
    simp at hph
  · intro _ _ _ hph
    simp at hph

theorem journal_extend (cfg : Barriers) (n : NodeState) (k : Nat) (h : JournalInv n) :
    JournalInv (stepExtend cfg n k).1 := by
  unfold stepExtend
  cases hu : n.usable <;> cases hk : n.key <;> simp only [hu, hk] <;> try exact h
  split
  · exact h.frame rfl rfl rfl rfl (Or.inl rfl)
  · exact h

theorem journal_restoreBoot (n : NodeState) (i : Nat) (h : JournalInv n) :
    JournalInv (stepRestoreBoot n i).1 := by
  unfold stepRestoreBoot
  cases hd : n.bootSnaps[i]? <;> simp only [hd]
  · exact h
  · exact h.frame rfl rfl rfl rfl (Or.inr rfl)

/-- Every event but a disk restore keeps the journal invariant. -/
theorem journal_step (cfg : Barriers) (hjc : cfg.journal = true) (n : NodeState) (e : Ev)
    (he : ∀ i, e ≠ .restoreDisk i) (h : JournalInv n) : JournalInv (step cfg n e).1 := by
  cases e with
  | start j => exact journal_start cfg hjc n j h
  | sync => exact journal_sync n h
  | decrypt => exact journal_decrypt cfg n h
  | hand => exact journal_hand n h
  | skip j => exact journal_skip cfg n j h
  | crash keep => exact journal_crash n keep h
  | reboot keep => exact journal_reboot n keep h
  | newStock => exact journal_newStock n h
  | extend k => exact journal_extend cfg n k h
  | snapDisk => exact h.frame rfl rfl rfl rfl (Or.inl rfl)
  | restoreDisk i => exact absurd rfl (he i)
  | snapBoot => exact h.frame rfl rfl rfl rfl (Or.inl rfl)
  | restoreBoot i => exact journal_restoreBoot n i h

theorem journalInv_init : JournalInv init where
  nodup := List.nodup_nil
  below := by intro _ _ _ hm; simp [init] at hm
  oldStock := by intro _ _ _ hm; simp [init] at hm
  hdrStock := by intro _ hh; simp [init] at hh
  wf := by simp [init]
  inflight := by intro _ _ _ hph; simp [init] at hph
  durable := by intro _ _ _ hph; simp [init] at hph

/-- **T14, journal barrier.** With the journal, in every trace without a restore of the disk
(any crashes at any step with torn journal tails, reboots, boot-memory rollbacks, any indices
chosen by the peer), no item is handed to the engine twice. -/
theorem T14_journal (cfg : Barriers) (hjc : cfg.journal = true) (evs : List Ev)
    (h : ∀ i, Ev.restoreDisk i ∉ evs) : (run cfg init evs).handed.Nodup :=
  (run_preserves cfg JournalInv (fun e => ∀ i, e ≠ .restoreDisk i)
    (fun n e he hn => journal_step cfg hjc n e he hn) evs init
    (fun _ he i hei => h i (hei ▸ he)) journalInv_init).nodup

/-- **T14 (stock used once).** In production (journal and key chain), in every trace of the use
rule over the journal model, with crashes of the node at any step (torn journal tails included),
restarts, reboots, lying or vanishing peers, and a rollback of EITHER its disk OR its boot memory
(not both), no item reaches the engine twice. -/
theorem T14 (evs : List Ev) (h : (∀ i, Ev.restoreBoot i ∉ evs) ∨ (∀ i, Ev.restoreDisk i ∉ evs)) :
    (run production init evs).handed.Nodup := by
  rcases h with h | h
  · exact T14_chain production rfl evs h
  · exact T14_journal production rfl evs h

/-! ## The assumptions are needed: concrete traces -/

/-- Take item 0, crash, take item 0 again. -/
def reuseAfterCrash : List Ev :=
  [.newStock, .extend 1, .start 0, .sync, .decrypt, .hand, .crash 0, .start 0, .sync, .decrypt, .hand]

/-- With neither barrier, a crash alone causes a reuse. -/
theorem no_barrier_reuse : ¬ (run ⟨false, false⟩ init reuseAfterCrash).handed.Nodup := by decide

/-- In production the same trace refuses the second take. -/
theorem production_refuses_after_crash :
    (run production init reuseAfterCrash).handed = [(0, 0, 0)] := by decide

/-- Snapshot the disk, take item 0, restore the disk, take item 0. -/
def diskRollback : List Ev :=
  [.newStock, .extend 1, .snapDisk, .start 0, .sync, .decrypt, .hand, .restoreDisk 0,
   .start 0, .sync, .decrypt, .hand]

/-- The journal alone does not survive a disk restore ... -/
theorem journal_alone_disk_rollback : ¬ (run ⟨true, false⟩ init diskRollback).handed.Nodup := by decide

/-- ... the chain does. -/
theorem production_disk_rollback : (run production init diskRollback).handed = [(0, 0, 0)] := by decide

/-- Snapshot boot memory, take item 0, roll boot memory back, take item 0. -/
def bootRollback : List Ev :=
  [.newStock, .extend 1, .snapBoot, .start 0, .sync, .decrypt, .hand, .restoreBoot 0,
   .start 0, .sync, .decrypt, .hand]

/-- The chain alone does not survive a boot-memory rollback ... -/
theorem chain_alone_boot_rollback : ¬ (run ⟨false, true⟩ init bootRollback).handed.Nodup := by decide

/-- ... the journal does. -/
theorem production_boot_rollback : (run production init bootRollback).handed = [(0, 0, 0)] := by decide

/-- Roll back both (a full snapshot of the node restored): nothing on the node can tell. -/
def fullRollback : List Ev :=
  [.newStock, .extend 1, .snapDisk, .snapBoot, .start 0, .sync, .decrypt, .hand, .restoreDisk 0,
   .restoreBoot 0, .start 0, .sync, .decrypt, .hand]

theorem full_rollback_reuse : ¬ (run production init fullRollback).handed.Nodup := by decide

/-! ## The boot id -/

structure BootInv (n : NodeState) : Prop where
  handed : ∀ b s j, (b, s, j) ∈ n.handed → (s, b) ∈ n.stocks
  key : ∀ k, n.key = some k → (k.stock, n.boot) ∈ n.stocks
  snaps : ∀ k, some k ∈ n.bootSnaps → (k.stock, n.boot) ∈ n.stocks
  phase : ∀ b s j, (n.phase = .appended b s j ∨ n.phase = .synced b s j ∨ n.phase = .opened b s j) →
    b = n.boot ∧ (s, b) ∈ n.stocks
  fresh : ∀ s b, (s, b) ∈ n.stocks → s < n.stockCtr
  unique : ∀ s b b', (s, b) ∈ n.stocks → (s, b') ∈ n.stocks → b = b'

theorem BootInv.frame {n n' : NodeState} (h : BootInv n) (hh : n'.handed = n.handed)
    (hs : n'.stocks = n.stocks) (hb : n'.boot = n.boot) (hc : n'.stockCtr = n.stockCtr)
    (hk : n'.key.map Key.stock = n.key.map Key.stock) (hsn : n'.bootSnaps = n.bootSnaps)
    (hp : n'.phase = n.phase ∨ n'.phase = .idle) : BootInv n' where
  handed := by intro b s j hm; rw [hh] at hm; rw [hs]; exact h.handed b s j hm
  key := by
    intro k hk'
    cases hk0 : n.key with
    | none => rw [hk', hk0] at hk; simp at hk
    | some k0 =>
      rw [hk', hk0] at hk
      simp only [Option.map_some, Option.some.injEq] at hk
      rw [hs, hb, hk]
      exact h.key k0 hk0
  snaps := by intro k hm; rw [hsn] at hm; rw [hs, hb]; exact h.snaps k hm
  phase := by
    intro b s j hph
    rcases hp with hp | hp
    · rw [hp] at hph; rw [hs, hb]; exact h.phase b s j hph
    · rw [hp] at hph; simp at hph
  fresh := by intro s b hm; rw [hs] at hm; rw [hc]; exact h.fresh s b hm
  unique := by intro s b b' h1 h2; rw [hs] at h1 h2; exact h.unique s b b' h1 h2

theorem boot_step (cfg : Barriers) (n : NodeState) (e : Ev) (h : BootInv n) : BootInv (step cfg n e).1 := by
  cases e with
  | start j =>
    show BootInv (stepStart cfg n j).1
    unfold stepStart
    cases hp : n.phase <;> cases hu : n.usable <;> simp only [hp, hu] <;> try exact h
    rename_i s
    split
    · exact h
    · split
      · exact h
      · obtain ⟨hd, k, _, hk, _, _, hks⟩ := usable_some hu
        refine ⟨h.handed, h.key, h.snaps, ?_, h.fresh, h.unique⟩
        intro b s' j' hph
        simp only [Phase.appended.injEq, reduceCtorEq, false_and, or_false] at hph
        obtain ⟨rfl, rfl, rfl⟩ := hph
        refine ⟨rfl, ?_⟩
        have := h.key k hk
        rw [hks] at this
        exact this
  | sync =>
    show BootInv (stepSync n).1
    unfold stepSync
    split
    next b s j hp =>
      refine ⟨h.handed, h.key, h.snaps, ?_, h.fresh, h.unique⟩
      intro b' s' j' hph
      simp only [reduceCtorEq, Phase.synced.injEq, false_or, or_false] at hph
      obtain ⟨rfl, rfl, rfl⟩ := hph
      exact h.phase b s j (Or.inl hp)
    next =>
      exact h.frame rfl rfl rfl rfl rfl rfl (Or.inl rfl)
  | decrypt =>
    show BootInv (stepDecrypt cfg n).1
    unfold stepDecrypt
    cases hp : n.phase <;> cases hk : n.key <;> simp only [hp, hk] <;> try exact h
    case synced.none b s j => exact h.frame rfl rfl rfl rfl (by simp [hk]) rfl (Or.inr rfl)
    case synced.some b s j k =>
      split
      · refine ⟨h.handed, ?_, h.snaps, ?_, h.fresh, h.unique⟩
        · intro k' hk'
          simp only [Option.some.injEq] at hk'
          rw [← hk']
          exact h.key k hk
        · intro b' s' j' hph
          simp only [reduceCtorEq, Phase.opened.injEq, false_or] at hph
          obtain ⟨rfl, rfl, rfl⟩ := hph
          exact h.phase b s j (Or.inr (Or.inl hp))
      · exact h.frame rfl rfl rfl rfl (by simp [hk]) rfl (Or.inr rfl)
  | hand =>
    show BootInv (stepHand n).1
    unfold stepHand
    cases hp : n.phase <;> simp only [hp] <;> try exact h
    case opened b s j =>
      obtain ⟨hb, hm⟩ := h.phase b s j (Or.inr (Or.inr hp))
      refine ⟨?_, h.key, h.snaps, ?_, h.fresh, h.unique⟩
      · intro b' s' j' hm'
        rw [List.mem_append] at hm'
        rcases hm' with hm' | hm'
        · exact h.handed b' s' j' hm'
        · simp only [List.mem_singleton, Prod.mk.injEq] at hm'
          obtain ⟨rfl, rfl, rfl⟩ := hm'
          rw [← hb]
          exact hm
      · intro _ _ _ hph
        simp at hph
  | skip j =>
    show BootInv (stepSkip cfg n j).1
    unfold stepSkip
    cases hp : n.phase <;> cases hu : n.usable <;> simp only [hp, hu] <;> try exact h
    split
    · exact h
    · refine h.frame rfl rfl rfl rfl ?_ rfl (Or.inl hp.symm)
      show (n.key.map (fun k => if cfg.chain then { k with use := j } else k)).map Key.stock = n.key.map Key.stock
      cases n.key with
      | none => rfl
      | some k => cases cfg.chain <;> rfl
  | crash keep => exact h.frame rfl rfl rfl rfl rfl rfl (Or.inr rfl)
  | reboot keep =>
    show BootInv (stepReboot n keep).1
    refine ⟨h.handed, ?_, ?_, ?_, h.fresh, h.unique⟩
    · intro _ hk; simp [stepReboot] at hk
    · intro _ hm; simp [stepReboot] at hm
    · intro _ _ _ hph; simp [stepReboot] at hph
  | newStock =>
    show BootInv (stepNewStock n).1
    unfold stepNewStock
    cases hp : n.phase <;> simp only [hp] <;> try exact h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro b s j hm
      exact List.mem_cons_of_mem _ (h.handed b s j hm)
    · intro k hk
      simp only [Option.some.injEq] at hk
      subst hk
      exact List.mem_cons_self
    · intro k hm
      exact List.mem_cons_of_mem _ (h.snaps k hm)
    · intro _ _ _ hph
      simp at hph
    · intro s b hm
      show s < n.stockCtr + 1
      rw [List.mem_cons] at hm
      rcases hm with hm | hm
      · simp only [Prod.mk.injEq] at hm
        obtain ⟨hm1, _⟩ := hm
        omega
      · have := h.fresh s b hm
        omega
    · intro s b b' h1 h2
      rw [List.mem_cons] at h1 h2
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · simp only [Prod.mk.injEq] at h1 h2
        rw [h1.2, h2.2]
      · simp only [Prod.mk.injEq] at h1
        obtain ⟨h1s, _⟩ := h1
        have := h.fresh s b' h2
        omega
      · simp only [Prod.mk.injEq] at h2
        obtain ⟨h2s, _⟩ := h2
        have := h.fresh s b h1
        omega
      · exact h.unique s b b' h1 h2
  | extend k =>
    show BootInv (stepExtend cfg n k).1
    unfold stepExtend
    cases hu : n.usable <;> cases hk : n.key <;> simp only [hu, hk] <;> try exact h
    split
    · exact h.frame rfl rfl rfl rfl (by simp [hk]) rfl (Or.inl rfl)
    · exact h
  | snapDisk => exact h.frame rfl rfl rfl rfl rfl rfl (Or.inl rfl)
  | restoreDisk i =>
    show BootInv (stepRestoreDisk n i).1
    unfold stepRestoreDisk
    cases hd : n.diskSnaps[i]? <;> simp only [hd]
    · exact h
    · exact h.frame rfl rfl rfl rfl rfl rfl (Or.inr rfl)
  | snapBoot =>
    refine ⟨h.handed, h.key, ?_, h.phase, h.fresh, h.unique⟩
    intro k hm
    have hm : some k ∈ n.bootSnaps ++ [n.key] := hm
    simp only [List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | hm
    · exact h.snaps k hm
    · exact h.key k hm.symm
  | restoreBoot i =>
    show BootInv (stepRestoreBoot n i).1
    unfold stepRestoreBoot
    cases hd : n.bootSnaps[i]? <;> simp only [hd]
    · exact h
    · rename_i k
      refine ⟨h.handed, ?_, h.snaps, ?_, h.fresh, h.unique⟩
      · intro k' hk'
        simp only at hk'
        subst hk'
        exact h.snaps k' (List.mem_of_getElem? hd)
      · intro _ _ _ hph
        simp at hph

theorem bootInv_init : BootInv init where
  handed := by intro _ _ _ hm; simp [init] at hm
  key := by intro _ hk; simp [init] at hk
  snaps := by intro _ hm; simp [init] at hm
  phase := by intro _ _ _ hph; simp [init] at hph
  fresh := by intro _ _ hm; simp [init] at hm
  unique := by intro _ _ _ hm; simp [init] at hm

/-- **The boot id.** In every trace (any events at all, restores included), every item handed to
the engine belongs to a stock made in the boot during which it was handed, and a stock is made
in exactly one boot. So a stock made in another boot, whether left from before a reboot or
brought back by a restore, is never used. -/
theorem T14_boot (cfg : Barriers) (evs : List Ev) :
    ∀ b s j, (b, s, j) ∈ (run cfg init evs).handed →
      (s, b) ∈ (run cfg init evs).stocks ∧ ∀ b', (s, b') ∈ (run cfg init evs).stocks → b' = b := by
  have inv := run_preserves cfg BootInv (fun _ => True) (fun n e _ hn => boot_step cfg n e hn) evs init
    (fun _ _ => trivial) bootInv_init
  intro b s j hm
  have h1 := inv.handed b s j hm
  exact ⟨h1, fun b' h2 => inv.unique s b' b h2 h1⟩

/-- The header check: a stock whose header carries another boot's id is never started. -/
theorem start_refused_other_boot (cfg : Barriers) (n : NodeState) (j : Nat) (hd : Hdr)
    (hh : n.disk.hdr = some hd) (hb : hd.boot ≠ n.boot) :
    stepStart cfg n j = (n, if n.phase = .idle then .refused .unusable else .refused .busy) := by
  have hu : n.usable = none := by
    unfold NodeState.usable
    rw [hh]
    cases n.key with
    | none => rfl
    | some k => simp [hb]
  unfold stepStart
  cases hp : n.phase <;> simp [hu]

/-! ## The pair -/

/-- The index both nodes use for a message, from the two claims exchanged inside the agreement:
the larger next index. If either node has no usable stock of the shape (`none`), the message is
preprocessed live: never refused. -/
def agreeIndex : Option Nat → Option Nat → Option Nat
  | some a, some b => some (max a b)
  | _, _ => none

/-- Both honest nodes compute the same index. -/
theorem agreeIndex_comm (x y : Option Nat) : agreeIndex x y = agreeIndex y x := by
  cases x <;> cases y <;> simp [agreeIndex, Nat.max_comm]

/-- **Never back**: whatever the peer claims, the agreed index is at or above this node's next
index, so `start` with it is never refused as `behind` (`honest_not_behind`); a lying peer can
only make the node skip forward. -/
theorem agreeIndex_never_back {mine j : Nat} {claim : Option Nat} (h : agreeIndex (some mine) claim = some j) :
    mine ≤ j := by
  cases claim with
  | none => simp [agreeIndex] at h
  | some c => simp only [agreeIndex, Option.some.injEq] at h; omega

theorem honest_not_behind (cfg : Barriers) (n : NodeState) (claim : Option Nat) (j : Nat)
    (h : agreeIndex (some (n.next cfg)) claim = some j) : ¬ j < n.next cfg := by
  have := agreeIndex_never_back h
  omega

/-- **Max + 1**: when the two journals' last consumed indices differ, both nodes use one more
than the larger. -/
theorem agreeIndex_max_succ (la lb : Nat) :
    agreeIndex (some (la + 1)) (some (lb + 1)) = some (max la lb + 1) := by
  simp only [agreeIndex, Option.some.injEq]
  omega

/-- No stock on either side: live preprocessing for this message. -/
theorem agreeIndex_none_left (x : Option Nat) : agreeIndex none x = none := rfl
theorem agreeIndex_none_right (x : Option Nat) : agreeIndex x none = none := by cases x <;> rfl

/-! ### Waste: each interruption costs at most one item per node

The pair, abstractly, round by round: both nodes compute j = max(nextA, nextB); each node either
completes (journals j and hands its item: next = j + 1, used + 1) or is interrupted by a crash or
a lost message (`cut`), in which case its journal entry for j may or may not have survived
(`Journal.crash_append`: at most the entry in flight is lost). -/

structure PairCount where
  nA : Nat
  nB : Nat
  uA : Nat
  uB : Nat
  cuts : Nat
  deriving DecidableEq, Repr

inductive RoundEnd where
  | used
  | cut (kept : Bool)
  deriving DecidableEq, Repr

/-- A node's (next, used, interruptions) after a round with agreed index `j`. -/
def RoundEnd.apply (j n u : Nat) : RoundEnd → Nat × Nat × Nat
  | .used => (j + 1, u + 1, 0)
  | .cut true => (j + 1, u, 1)
  | .cut false => (n, u, 1)

def pairRound (p : PairCount) (a b : RoundEnd) : PairCount :=
  let j := max p.nA p.nB
  let ra := a.apply j p.nA p.uA
  let rb := b.apply j p.nB p.uB
  ⟨ra.1, rb.1, ra.2.1, rb.2.1, p.cuts + ra.2.2 + rb.2.2⟩

def pairRounds (p : PairCount) : List (RoundEnd × RoundEnd) → PairCount
  | [] => p
  | r :: rs => pairRounds (pairRound p r.1 r.2) rs

theorem pairRound_inv (p : PairCount) (a b : RoundEnd)
    (h : max p.nA p.nB ≤ p.uA + p.cuts ∧ max p.nA p.nB ≤ p.uB + p.cuts) :
    let q := pairRound p a b
    max q.nA q.nB ≤ q.uA + q.cuts ∧ max q.nA q.nB ≤ q.uB + q.cuts := by
  cases a with
  | used => cases b with
    | used => simp only [pairRound, RoundEnd.apply]; omega
    | cut kb => cases kb <;> simp only [pairRound, RoundEnd.apply] <;> omega
  | cut ka => cases ka <;> cases b with
    | used => simp only [pairRound, RoundEnd.apply]; omega
    | cut kb => cases kb <;> simp only [pairRound, RoundEnd.apply] <;> omega

/-- **Waste bound.** Starting from fresh stocks, after any sequence of rounds, each node's next
index exceeds the number of items it handed to its engine by at most the number of
interruptions (crashes and lost messages, of either node): each interruption wastes at most one
item of each node. A lying peer is not bounded (it can claim any index and exhaust the stock:
availability only, the message then goes live). -/
theorem waste_bound (rs : List (RoundEnd × RoundEnd)) :
    let p := pairRounds ⟨0, 0, 0, 0, 0⟩ rs
    p.nA ≤ p.uA + p.cuts ∧ p.nB ≤ p.uB + p.cuts := by
  have key : ∀ (rs : List (RoundEnd × RoundEnd)) (p : PairCount),
      (max p.nA p.nB ≤ p.uA + p.cuts ∧ max p.nA p.nB ≤ p.uB + p.cuts) →
      let q := pairRounds p rs
      max q.nA q.nB ≤ q.uA + q.cuts ∧ max q.nA q.nB ≤ q.uB + q.cuts := by
    intro rs
    induction rs with
    | nil => intro p h; exact h
    | cons r rs ih => intro p h; exact ih _ (pairRound_inv p r.1 r.2 h)
  have := key rs ⟨0, 0, 0, 0, 0⟩ (by simp)
  simp only at this ⊢
  omega

/-! ## SPECIFICATION: the `stockUse` engine instruction

NOT WIRED IN. Engine.lean is unchanged; this section is what it gains when the instruction is
added (after the pending branch with a new instruction is merged). Plain text first, then the
standalone definitions the owner can paste or call.

  Opcode. The next free opcode after the pending branch's instruction (`opStockUse`, written 22
  here provisionally; renumber if 22 is taken).

  Encoding (all public, no starred payload, so the whole instruction is part of the agreed
  skeleton): opcode, shape id (Format.ShapeId.enc), u64 index, agreed hash (32 bytes raw).
  `encStockUse` / `decStockUse`, round trip `stockUse_enc`.

  The per-message agreement. Before the batch that runs a stocked circuit, the two nodes
  exchange claims (`Format.encClaim`: their next index for the shape, or none) in an ordinary
  `exchange` of the previous batch (a label of its own, e.g. a new RevealKind `stockClaim`; the
  claims are public: indices reveal nothing about contacts or messages). Each node computes
  j = agreeIndex(mine, peer's) and, if j is some, puts `stockUse shape j agreedHash(j)` in its
  next batch right before the `run` of that circuit; if none, or if its own store says the item
  is absent, it builds the batch without `stockUse` (live preprocessing). The skeleton
  agreement (Engine design note item 4) then confirms byte for byte that both nodes use the same
  shape, the same index and two halves of the same item (the agreed hash); a mismatch (a lying
  peer, a stock on one side only) rejects the batch before any engine call, and the message is
  retried live.

  check (added to Engine.check; the context gains a `StockCtx`):
    stockUse shape index hash: refused unless the circuit is known (sigs), the hash has 32
    bytes, no item is armed, index >= floor(shape) (never back within the session) and
    index < 2^64; then floor(shape) := index + 1 and the item is ARMED for that circuit.
    `checkStockUse`.
    run out name copies input: if an item is armed for `name`, copies must be 1 and the item is
    consumed (disarmed); otherwise as today. `checkRunArmed`.
    end of batch: refused if an item is still armed (it would be taken and not used).
    `batchEndOk`.
  Theorem for the session: `stockUses_nodup`: the (shape, index) pairs of the accepted
  `stockUse` instructions of a session are pairwise distinct (a fourth, per-session barrier,
  on top of the store's).

  Execution (shell, Rust): after the agreement and checkBatch, before the batch's first engine
  call, for each `stockUse`: `Store::take_expect(shape, index, hash)` (journal + fsync + key
  erased, then decrypt and verify), then the engine's `import_preprocessing` (C ABI, not built)
  binds the item to the next `ea_bool_run` of that circuit. If the store refuses (behind, absent,
  erased, corrupt), the shell rejects the batch like an unusable one, and the peer's matching call
  fails; the item index is consumed on the side that took it, never reused, and the message goes
  live. Channels.stockJournal (`append`, `sync`, `read`) is the Lean-side binding of the same
  journal for when the use rule moves into the controller.
-/

/-- Provisional opcode of `stockUse`. -/
def opStockUse : UInt8 := 22

structure StockUse where
  shape : ShapeId
  index : Nat
  agreed : Bytes
  deriving DecidableEq, Repr

def StockUse.Bounded (u : StockUse) : Prop := u.shape.Bounded ∧ u.index < B64 ∧ u.agreed.length = 32

def encStockUse (u : StockUse) : Bytes := opStockUse :: (u.shape.enc ++ (Enc.u64 u.index ++ u.agreed))

def decStockUse : Dec StockUse := do
  let op ← Dec.byte
  if op = opStockUse then
    let sh ← decShape
    let i ← Dec.u64
    let a ← Dec.take 32
    pure ⟨sh, i, a⟩
  else Dec.fail

theorem stockUse_enc (u : StockUse) (hu : u.Bounded) (rest : Bytes) :
    decStockUse (encStockUse u ++ rest) = some (u, rest) := by
  obtain ⟨hs, hi, ha⟩ := hu
  simp only [decStockUse, encStockUse, List.cons_append, List.append_assoc, Dec.bind_apply, Dec.byte,
    if_true, shape_enc _ hs, u64_enc _ hi, take_enc 32 _ _ ha, Dec.pure_apply]

/-- The session's stock context (the part of `Engine.Ctx` that `stockUse` adds): per shape (by
its encoding) the least index the session may still use, and the item armed for the next run. -/
structure StockCtx where
  floor : List (Bytes × Nat) := []
  armed : Option (Bytes × Nat) := none

def StockCtx.floorOf (c : StockCtx) (key : Bytes) : Nat := (c.floor.lookup key).getD 0

/-- The `check` rule of `stockUse`. -/
def checkStockUse (sigs : Bytes → Option Sig) (c : StockCtx) (u : StockUse) : Option StockCtx :=
  if (sigs u.shape.circuit).isSome ∧ u.agreed.length = 32 ∧ c.armed = none ∧
      c.floorOf u.shape.enc ≤ u.index ∧ u.index < B64 then
    some { floor := (u.shape.enc, u.index + 1) :: c.floor, armed := some (u.shape.circuit, u.index) }
  else none

/-- The addition to `check` of `run`: an armed item is consumed by the next run of its circuit,
which must then be a single copy. -/
def checkRunArmed (c : StockCtx) (name : Bytes) (copies : Nat) : Option StockCtx :=
  match c.armed with
  | some (n, _) => if n = name then (if copies = 1 then some { c with armed := none } else none) else some c
  | none => some c

/-- At the end of a batch no item may be left armed. -/
def batchEndOk (c : StockCtx) : Bool := c.armed.isNone

theorem floorOf_cons_self (l : List (Bytes × Nat)) (key : Bytes) (v : Nat) (a : Option (Bytes × Nat)) :
    StockCtx.floorOf { floor := (key, v) :: l, armed := a } key = v := by
  simp [StockCtx.floorOf, List.lookup]

theorem floorOf_cons_other (l : List (Bytes × Nat)) (key key' : Bytes) (v : Nat) (a a' : Option (Bytes × Nat))
    (hne : key' ≠ key) :
    StockCtx.floorOf { floor := (key, v) :: l, armed := a } key' = StockCtx.floorOf { floor := l, armed := a' } key' := by
  have hb : (key' == key) = false := by simpa using hne
  simp [StockCtx.floorOf, List.lookup, hb]

theorem checkStockUse_spec (sigs : Bytes → Option Sig) (c c' : StockCtx) (u : StockUse)
    (h : checkStockUse sigs c u = some c') :
    c.floorOf u.shape.enc ≤ u.index ∧ c'.floorOf u.shape.enc = u.index + 1 ∧
      (∀ key, key ≠ u.shape.enc → c'.floorOf key = c.floorOf key) ∧ c.armed = none := by
  unfold checkStockUse at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨hc.2.2.2.1, floorOf_cons_self _ _ _ _, ?_, hc.2.2.1⟩
    intro key hne
    exact floorOf_cons_other _ _ _ _ _ c.armed hne
  · simp at h

/-- Uses accepted one after another in a session, each consumed by its run before the next. -/
def acceptsAll (sigs : Bytes → Option Sig) : StockCtx → List StockUse → Prop
  | _, [] => True
  | c, u :: us => ∃ c', checkStockUse sigs c u = some c' ∧ acceptsAll sigs { c' with armed := none } us

theorem acceptsAll_above (sigs : Bytes → Option Sig) :
    ∀ (us : List StockUse) (c : StockCtx), acceptsAll sigs c us → ∀ u ∈ us, c.floorOf u.shape.enc ≤ u.index
  | [], _, _, u, hu => by simp at hu
  | v :: us, c, ⟨c', hc, hrest⟩, u, hu => by
    obtain ⟨h1, h2, h3, _⟩ := checkStockUse_spec sigs c c' v hc
    rcases List.mem_cons.mp hu with rfl | hu
    · exact h1
    · have := acceptsAll_above sigs us _ hrest u hu
      have hfl : StockCtx.floorOf { c' with armed := none } u.shape.enc = c'.floorOf u.shape.enc := rfl
      rw [hfl] at this
      by_cases hk : u.shape.enc = v.shape.enc
      · rw [hk, h2] at this; rw [hk]; omega
      · rw [h3 _ hk] at this; exact this

/-- **Within a session, no (shape, index) is used twice** (the per-session barrier of the
specified `check` rule). -/
theorem stockUses_nodup (sigs : Bytes → Option Sig) :
    ∀ (us : List StockUse) (c : StockCtx), acceptsAll sigs c us →
      (us.map fun u => (u.shape.enc, u.index)).Nodup
  | [], _, _ => List.nodup_nil
  | v :: us, c, ⟨c', hc, hrest⟩ => by
    obtain ⟨_, h2, _, _⟩ := checkStockUse_spec sigs c c' v hc
    refine List.nodup_cons.mpr ⟨?_, stockUses_nodup sigs us _ hrest⟩
    intro hm
    rw [List.mem_map] at hm
    obtain ⟨u, hu, he⟩ := hm
    simp only [Prod.mk.injEq] at he
    have := acceptsAll_above sigs us _ hrest u hu
    have hfl : StockCtx.floorOf { c' with armed := none } u.shape.enc = c'.floorOf u.shape.enc := rfl
    rw [hfl, he.1, h2] at this
    omega

end TlsMpc.Node.Stock
