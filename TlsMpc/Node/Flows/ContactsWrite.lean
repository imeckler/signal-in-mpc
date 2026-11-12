import TlsMpc.Node.Flows.ContactsTable
import TlsMpc.Node.Flows.Random

/-!
# T10: a contact's state written to the database nodes under a fresh joint nonce

REORGANIZATION_PLAN.md section 8.1, T10, stage S9. The database write itself (`DbCall.writeBlob`,
`dbSubmit` in `PublicServiceController.lean` line 473) is the controller's; what these flows
contribute is the blob and its nonce. Today (`PublicServiceController.lean` lines 431-434, 482-484):
op 33 gives 32 jointly random bytes, the nonce is their first 8 (refused if all 255), op 38 seals
the state with that nonce as its version, and the blob written is nonce ‖ check ‖ ciphertext. The
controller does not refuse a nonce it has used before (NEEDS_REVIEW 3b; plan R13).

`writeScript`: `Random.joint` (P-RAND), nonce := its first 8 bytes; refused unless it is a valid
version AND not in `used`, the session's nonces so far (R13: distinct within a session); then
`sealScript` under it. Returns (nonce, nonce ‖ check ‖ ciphertext). The controller adds the nonce
to `used` after each write (`useNonce`).

PROVED (against ANY adversary, any engine state): `write_fresh` (T10's nonce and blob shape): every
result (v, blob) has v a valid version (8 bytes, not 2^64 − 1), v not in `used`, and
blob = v ‖ sealReply size out for the opened `sealedBlob` bundle `out` (check ‖ ciphertext; its
value is `seal_disclosure` / `seal_honest`). `used_nodup`: the session's nonce list stays duplicate
free. The nonce is the first 8 bytes of the value `Random.joint` returned in the same script
(`Random.prand_accepted`, P-RAND (a)/(b)).

NOT HERE: the version-per-contact counter ("increase by one per acknowledged write") is the
controller's database bookkeeping, not a worker flow; T3 for the composed script needs a generic
`withAdv`-over-`bind` lemma (the model has none yet): the composition's releases are those of
`Random.joint` (prand_disclosure) followed by those of the seal (seal_disclosure).
-/

namespace TlsMpc.Node.Flows.Contacts

open TlsMpc.Node.Engine

/-- The nonce: the first 8 bytes of a joint random value. -/
def nonceOf (j : Bytes) : B8 := (j.take 8).map UInt8.toBitVec

/-- **A state write's worker part.** `nonceSlot`, `valueSlot`: this party's random contribution to
`Random.joint`; `used`: this session's nonces so far. -/
def writeScript (hash : Bytes → Bytes) (me : Party) (nonceSlot valueSlot : Nat) (used : List B8) (n : Nat)
    (key state : BoolH) (size : Nat) : Script (B8 × B8) :=
  (Random.joint hash me nonceSlot valueSlot).bind fun j =>
    if versionOk (nonceOf j) = true ∧ nonceOf j ∉ used then
      (sealScript n key state size (nonceOf j)).bind fun r => .done (nonceOf j, nonceOf j ++ r)
    else .abort "state nonce"

/-- The session's nonces after a write with nonce `v`. -/
def useNonce (used : List B8) (v : B8) : List B8 := v :: used

/-- What every write returns. -/
def WriteOk (used : List B8) (size : Nat) (x : B8 × B8) : Prop :=
  versionOk x.1 = true ∧ x.1 ∉ used ∧ ∃ out : Bits, x.2 = x.1 ++ sealReply size out

theorem Leaves.bind_of {α β : Type} {P : α → Prop} {Q : β → Prop} (f : α → Script β)
    (hf : ∀ a, P a → Leaves Q (f a)) : ∀ (s : Script α), Leaves P s → Leaves Q (s.bind f)
  | .done a, h => by cases h with | done _ ha => exact hf a ha
  | .abort r, _ => Leaves.abort r
  | .step i k, h => by
    cases h with
    | step _ _ hk => exact Leaves.step i _ (fun r => Leaves.bind_of f hf (k r) (hk r))

/-- Every result of a seal is `sealReply size out` for the bundle `out` it opened. -/
theorem seal_leaves (n : Nat) (key state : BoolH) (size : Nat) (version : B8) :
    Leaves (fun r => ∃ out : Bits, r = sealReply size out) (sealScript n key state size version) := by
  unfold sealScript
  split
  · refine Leaves.seqs ?_ _
    refine Leaves.step _ _ (fun r => ?_)
    cases r with
    | bits b => exact Leaves.seqs (Leaves.done _ ⟨b, rfl⟩) _
    | _ => exact Leaves.abort _
  · exact Leaves.abort _

theorem write_leaves (hash : Bytes → Bytes) (me : Party) (nonceSlot valueSlot : Nat) (used : List B8) (n : Nat)
    (key state : BoolH) (size : Nat) :
    Leaves (WriteOk used size) (writeScript hash me nonceSlot valueSlot used n key state size) := by
  unfold writeScript
  refine Leaves.bind _ (fun j => ?_) _
  split
  · next h =>
    refine Leaves.bind_of _ (fun r hr => ?_) _ (seal_leaves n key state size (nonceOf j))
    obtain ⟨out, rfl⟩ := hr
    exact Leaves.done _ ⟨h.1, h.2, out, rfl⟩
  · exact Leaves.abort _

/-- **T10 (what the worker flows contribute).** Against any adversary: a write's nonce is a valid
version not used before in the session, and its blob is the nonce followed by the seal's reply
(check ‖ ciphertext of the opened `sealedBlob` bundle). -/
theorem write_fresh (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal) (vD : List Release)
    (nonceSlot valueSlot : Nat) (used : List B8) (n : Nat) (key state : BoolH) (size : Nat) (x : B8 × B8)
    (h : (withAdv E me adv (writeScript E.hash me nonceSlot valueSlot used n key state size) σ I vD).result = some x) :
    versionOk x.1 = true ∧ x.1 ∉ used ∧ ∃ out : Bits, x.2 = x.1 ++ sealReply size out :=
  Leaves.result E me adv _ (write_leaves E.hash me nonceSlot valueSlot used n key state size) σ I vD x h

/-- **State nonces never repeat within a session**: adding each write's nonce keeps the list
duplicate free (`write_fresh` gives `v ∉ used`). -/
theorem used_nodup (used : List B8) (v : B8) (hu : used.Nodup) (hv : v ∉ used) : (useNonce used v).Nodup :=
  List.nodup_cons.mpr ⟨hv, hu⟩

end TlsMpc.Node.Flows.Contacts
