import Std

/-!
Metadata guards for a five-party refresh transaction with abort.

This is a small pure state machine, not distributed consensus or durable I/O.
`certificateChecked` and `backendChecked` represent successful external
verification, not locally trusted input bits. In a real adapter, signature
checks, non-equivocation journals, backend checks, durable writes and agreement
on the descriptor must establish those facts before `advance` may be called.

The five acknowledgements deliberately require every party. A missing party
can cause abort, which matches the requested availability policy. Acknowledging
does not prove erasure or honest behavior.

Proactive protection against two mobile corruptions per epoch is REQUIRED.
The exposure model below records the corresponding environmental assumption;
it does not establish that a particular refresh protocol realizes it. In
particular, advancing this metadata head is not evidence that old runtime
state has been erased or that a new protected period can begin.
-/

namespace TlsMpc.Sharing

structure Context where
  protocolVersion : String
  committeeDigest : String
  sharingDomain : String
  schemaDigest : String
  programDigest : String
  deriving DecidableEq, Repr

structure Head where
  context : Context
  epoch : Nat
  manifestDigest : String
  deriving DecidableEq, Repr

/-- All fields must be included in the canonical signed encoding. -/
structure RefreshDescriptor where
  context : Context
  fromEpoch : Nat
  toEpoch : Nat
  previousManifest : String
  nextManifest : String
  batchId : String
  preprocessingReservation : String
  deriving DecidableEq, Repr

def RefreshDescriptor.matches (request : RefreshDescriptor) (head : Head) : Prop :=
  request.context = head.context ∧ request.fromEpoch = head.epoch ∧
    request.toEpoch = head.epoch + 1 ∧ request.previousManifest = head.manifestDigest

instance (request : RefreshDescriptor) (head : Head) :
    Decidable (request.matches head) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

structure CommitEvidence where
  descriptor : RefreshDescriptor
  prepared : Fin 5 → Bool
  certificateChecked : Bool
  backendChecked : Bool

def CommitEvidence.acceptable (evidence : CommitEvidence)
    (request : RefreshDescriptor) : Prop :=
  evidence.descriptor = request ∧ evidence.certificateChecked = true ∧
    evidence.backendChecked = true ∧ ∀ i, evidence.prepared i = true

instance (evidence : CommitEvidence) (request : RefreshDescriptor) :
    Decidable (evidence.acceptable request) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ ∀ _, _))

def RefreshDescriptor.nextHead (request : RefreshDescriptor) : Head :=
  { context := request.context, epoch := request.toEpoch,
    manifestDigest := request.nextManifest }

def advance (head : Head) (request : RefreshDescriptor)
    (evidence : CommitEvidence) : Head :=
  if request.matches head ∧ evidence.acceptable request then request.nextHead else head

theorem advance_rejected (head : Head) (request : RefreshDescriptor)
    (evidence : CommitEvidence)
    (h : ¬ (request.matches head ∧ evidence.acceptable request)) :
    advance head request evidence = head := by
  simp [advance, h]

theorem advance_accepted (head : Head) (request : RefreshDescriptor)
    (evidence : CommitEvidence) (hmatch : request.matches head)
    (hcheck : evidence.acceptable request) :
    advance head request evidence = request.nextHead := by
  simp [advance, hmatch, hcheck]

theorem advance_epoch (head : Head) (request : RefreshDescriptor)
    (evidence : CommitEvidence) :
    (advance head request evidence).epoch = head.epoch ∨
      (advance head request evidence).epoch = head.epoch + 1 := by
  by_cases h : request.matches head ∧ evidence.acceptable request
  · right
    rw [advance_accepted head request evidence h.1 h.2]
    exact h.1.2.2.1
  · left
    rw [advance_rejected head request evidence h]

theorem advance_context (head : Head) (request : RefreshDescriptor)
    (evidence : CommitEvidence) :
    (advance head request evidence).context = head.context := by
  by_cases h : request.matches head ∧ evidence.acceptable request
  · rw [advance_accepted head request evidence h.1 h.2]
    exact h.1.1
  · rw [advance_rejected head request evidence h]

theorem accepted_requires_all_five (head : Head) (request : RefreshDescriptor)
    (evidence : CommitEvidence) (changed : advance head request evidence ≠ head) :
    ∀ i, evidence.prepared i = true := by
  by_cases h : request.matches head ∧ evidence.acceptable request
  · exact h.2.2.2.2
  · exact False.elim (changed (advance_rejected head request evidence h))

theorem replay_rejected (head : Head) (request : RefreshDescriptor)
    (evidence : CommitEvidence) (hmatch : request.matches head)
    (hcheck : evidence.acceptable request) :
    advance (advance head request evidence) request evidence =
      advance head request evidence := by
  rw [advance_accepted head request evidence hmatch hcheck]
  apply advance_rejected
  intro h
  have hfrom := hmatch.2.1
  have hto := hmatch.2.2.1
  have hsame := h.1.2.1
  change request.fromEpoch = request.toEpoch at hsame
  omega

theorem skipped_epoch_rejected (head : Head) (request : RefreshDescriptor)
    (evidence : CommitEvidence) (h : request.toEpoch ≠ head.epoch + 1) :
    advance head request evidence = head := by
  apply advance_rejected
  intro accepted
  exact h accepted.1.2.2.1

/-!
Corruption accounting follows the standard proactive model: a compromise
during the transition from e to e+1 is charged to BOTH periods. These predicates
are historical exposure events, not the set of machines currently controlled
by an attacker. Recovery never deletes an earlier event. The model includes no
global lifetime bound and makes no assumption that corruption is observable.

The security argument must justify how actual disk/memory/transcript/runtime
exposures map to these events, including old backups and failed transitions.
-/

namespace Exposure

abbrev Party := Fin 5

structure Trace where
  inPeriod : Nat → Party → Prop
  /-- `inRefresh e i`: party i is exposed during the e to e+1 transition. -/
  inRefresh : Nat → Party → Prop

def Trace.accounted (trace : Trace) (epoch : Nat) (party : Party) : Prop :=
  trace.inPeriod epoch party ∨ trace.inRefresh epoch party ∨
    ∃ previous, epoch = previous + 1 ∧ trace.inRefresh previous party

/-- No triple of distinct exposed parties; equivalent to cardinality at most two. -/
def AtMostTwo (exposed : Party → Prop) : Prop :=
  ∀ a b c, exposed a → exposed b → exposed c → a = b ∨ a = c ∨ b = c

def Trace.admissible (trace : Trace) : Prop :=
  ∀ epoch, AtMostTwo (trace.accounted epoch)

theorem period_is_accounted (trace : Trace) (epoch : Nat) (party : Party)
    (h : trace.inPeriod epoch party) : trace.accounted epoch party :=
  Or.inl h

theorem refresh_charged_source (trace : Trace) (epoch : Nat) (party : Party)
    (h : trace.inRefresh epoch party) : trace.accounted epoch party :=
  Or.inr (Or.inl h)

theorem refresh_charged_target (trace : Trace) (epoch : Nat) (party : Party)
    (h : trace.inRefresh epoch party) : trace.accounted (epoch + 1) party :=
  Or.inr (Or.inr ⟨epoch, rfl, h⟩)

theorem three_distinct_exposures_reject (trace : Trace) (epoch : Nat)
    (a b c : Party) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : trace.accounted epoch a) (hb : trace.accounted epoch b)
    (hc : trace.accounted epoch c) : ¬ trace.admissible := by
  intro h
  rcases h epoch a b c ha hb hc with h | h | h
  · exact hab h
  · exact hac h
  · exact hbc h

theorem refresh_and_next_period_share_budget (trace : Trace) (epoch : Nat)
    (a b c : Party) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : trace.inRefresh epoch a) (hb : trace.inPeriod (epoch + 1) b)
    (hc : trace.inPeriod (epoch + 1) c) : ¬ trace.admissible := by
  exact three_distinct_exposures_reject trace (epoch + 1) a b c hab hac hbc
    (refresh_charged_target trace epoch a ha)
    (period_is_accounted trace (epoch + 1) b hb)
    (period_is_accounted trace (epoch + 1) c hc)

/-- Adding recorded exposures cannot restore a previously violated bound. -/
def Trace.extends (later earlier : Trace) : Prop :=
  (∀ e i, earlier.inPeriod e i → later.inPeriod e i) ∧
    (∀ e i, earlier.inRefresh e i → later.inRefresh e i)

theorem accounted_monotone (later earlier : Trace) (h : later.extends earlier)
    (epoch : Nat) (party : Party) :
    earlier.accounted epoch party → later.accounted epoch party := by
  intro hx
  rcases hx with hx | hx | ⟨previous, he, hx⟩
  · exact Or.inl (h.1 epoch party hx)
  · exact Or.inr (Or.inl (h.2 epoch party hx))
  · exact Or.inr (Or.inr ⟨previous, he, h.2 previous party hx⟩)

theorem violation_persists (later earlier : Trace) (h : later.extends earlier)
    (bad : ¬ earlier.admissible) : ¬ later.admissible := by
  intro hlater
  apply bad
  intro e a b c ha hb hc
  exact hlater e a b c
    (accounted_monotone later earlier h e a ha)
    (accounted_monotone later earlier h e b hb)
    (accounted_monotone later earlier h e c hc)

/-- A model witness: one rotating exposed party, and clean refresh phases. -/
def rotating : Trace where
  inPeriod e party := e % 5 = party.val
  inRefresh _ _ := False

theorem rotating_admissible : rotating.admissible := by
  intro e a b _ ha hb _
  have ha' : e % 5 = a.val := by simpa [Trace.accounted, rotating] using ha
  have hb' : e % 5 = b.val := by simpa [Trace.accounted, rotating] using hb
  exact Or.inl (Fin.ext (ha'.symm.trans hb'))

theorem rotating_exposes_every_party :
    ∀ party, ∃ epoch, rotating.accounted epoch party := by
  intro party
  refine ⟨party.val, Or.inl ?_⟩
  exact Nat.mod_eq_of_lt party.isLt

end Exposure

/-!
Operational conditions for an honest local process to resume after a boundary.
These are obligations of the integration, not facts established by checking
peer signatures. In particular a malicious peer cannot be forced to erase its
view: its retained view remains accounted for by the security model. Recovery
of an honest process must actually establish its local conditions below.

All unused preprocessing is discarded by the proposed initial integration;
`freshCorrelationState` also covers PRSS/input PRNG seeds, daBits/edaBits,
triple pools, OT state and MAC-key contexts if used by the selected backend.
-/

structure BoundaryReadiness where
  committedHeadAgreed : Bool
  localOldMaterialRetired : Bool
  freshPrivateEntropy : Bool
  freshCorrelationState : Bool
  internalTransportRekeyed : Bool
  epochAuthenticationReady : Bool
  rollbackCheckpointAnchored : Bool
  cleanupAcknowledged : Fin 5 → Bool

def BoundaryReadiness.mayResume (ready : BoundaryReadiness) : Prop :=
  ready.committedHeadAgreed = true ∧ ready.localOldMaterialRetired = true ∧
    ready.freshPrivateEntropy = true ∧ ready.freshCorrelationState = true ∧
    ready.internalTransportRekeyed = true ∧ ready.epochAuthenticationReady = true ∧
    ready.rollbackCheckpointAnchored = true ∧ ∀ i, ready.cleanupAcknowledged i = true

theorem resume_requires_retirement (ready : BoundaryReadiness)
    (h : ready.mayResume) : ready.localOldMaterialRetired = true :=
  h.2.1

theorem resume_requires_fresh_correlations (ready : BoundaryReadiness)
    (h : ready.mayResume) : ready.freshCorrelationState = true :=
  h.2.2.2.1

theorem resume_requires_transport_rekey (ready : BoundaryReadiness)
    (h : ready.mayResume) : ready.internalTransportRekeyed = true :=
  h.2.2.2.2.1

theorem resume_requires_all_cleanup_receipts (ready : BoundaryReadiness)
    (h : ready.mayResume) : ∀ i, ready.cleanupAcknowledged i = true :=
  h.2.2.2.2.2.2.2

theorem retained_material_blocks_resume (ready : BoundaryReadiness)
    (h : ready.localOldMaterialRetired = false) : ¬ ready.mayResume := by
  intro allowed
  have retired := resume_requires_retirement ready allowed
  simp [h] at retired

end TlsMpc.Sharing
