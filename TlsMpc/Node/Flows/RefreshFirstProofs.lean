import TlsMpc.Node.Flows.RefreshKemProofs
import TlsMpc.KernelSpecs.EstablishDevices

/-!
# T4-REFRESH, the first message: the scratch hands the send exactly `establish-session`'s records

REORGANIZATION_PLAN.md stage S15. No I/O; no emitter imports this module.

`EstablishFirst.firstMessage_envelope` (and `EstablishDevices.openedEnvelopes_first`, device by
device) needs `wired`: `bundle-seal`'s `conversation` and `pending` inputs are `establish-session`'s
outputs 1 and 2. The script cuts them from the session's output bundle (`sessionScript`: handles
`n + 29`, `n + 30`, bits `8 … 8 + 8·(cert + 319)` and the next `8·1616`) and keeps them, unchanged,
in the scratch (`Device.conversation`, `Device.pending`) for the send (S13's `Flow.Send.sealDevices`,
a parameter).

PROVED:
  * `kept_outputs`: those two slices are exactly the kernel's outputs 1 and 2 (given the session
    kernel's output widths, `SessionWidths`, the pinned layout);
  * `first_wired`: so, when the send's seal reads its `conversation` and `pending` from the handles
    the scratch hands it (the parameter's specification) and both opened statuses are 255,
    `EstablishDevices.wired` HOLDS; `first_envelopes`: the opened envelopes are, device by device,
    `EstablishFirst.Reference.firstEnvelope` of that device's agreements, ids and keys;
  * `stored_record`: after the commit the stored record is the conversation without its
    certificate, and an accepted conversation is the session's certificate input followed by it
    (`ByteAuth.release_accept`): a send that prefixes the account's certificate (the same handle
    the session was given) rebuilds exactly the session's conversation.
-/

namespace TlsMpc.Node.Flows.Refresh

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts
open Std.Tactic.BVDecide
open TlsMpc.KernelSpecs.EstablishDevices (DeviceSession DeviceSeal wired firstOf)

/-- The conversation the script keeps, from the session's output bytes. -/
def keptConversation (out : B8) (cert : Nat) : B8 := fieldAt out 1 (cert + recordBytes)
/-- The pending record the script keeps. -/
def keptPending (out : B8) (cert : Nat) : B8 := fieldAt out (1 + (cert + recordBytes)) pendingBytes

/-- The output widths of `establish-session CERT ONETIME` (status, conversation, pending,
receiver: the pinned layout). -/
def SessionWidths (cert : Nat) (oneTime : Bool) : Prop :=
  ∀ a, (kvals (TlsMpc.EstablishKernel.establishSession cert oneTime) a).map List.length = [1, cert + 319, 1616, 192]

/-- **The kept slices are the session's records.** -/
theorem kept_outputs (cert : Nat) (oneTime : Bool) (hW : SessionWidths cert oneTime) (a : BVExpr.Assignment) :
    keptConversation (kvals (TlsMpc.EstablishKernel.establishSession cert oneTime) a).flatten cert =
        (kvals (TlsMpc.EstablishKernel.establishSession cert oneTime) a).getD 1 [] ∧
      keptPending (kvals (TlsMpc.EstablishKernel.establishSession cert oneTime) a).flatten cert =
        (kvals (TlsMpc.EstablishKernel.establishSession cert oneTime) a).getD 2 [] :=
  ⟨fieldAt_get' _ _ (hW a) 1 1 (cert + recordBytes) rfl rfl,
   fieldAt_get' _ _ (hW a) 2 (1 + (cert + recordBytes)) pendingBytes (by simp [recordBytes]) rfl⟩

/-- **`wired`, for the script.** -/
theorem first_wired (cert content : Nat) (s : DeviceSession) (d : DeviceSeal)
    (hW : SessionWidths cert d.withOneTime)
    (established : (s.outputs cert d.withOneTime).getD 0 [] = [255])
    (hconv : d.input cert content "conversation" = keptConversation (s.outputs cert d.withOneTime).flatten cert)
    (hpend : d.input cert content "pending" = keptPending (s.outputs cert d.withOneTime).flatten cert)
    (opened : (d.outputs cert content).getD 0 [] = [255]) : wired cert content (s, d) := by
  have k := kept_outputs cert d.withOneTime hW s.assign
  exact ⟨established, hconv.trans k.1, hpend.trans k.2, opened⟩

/-- **The first message after a refresh**, per device: when each device's seal reads the records
the scratch handed it, the opened envelopes are the reference first PreKey messages
(`EstablishDevices.openedEnvelopes_first`, its `wired` discharged by `first_wired`). -/
theorem first_envelopes (cert content : Nat) (ps : List (DeviceSession × DeviceSeal))
    (hb : ∀ p ∈ ps, p.2.bounded cert content)
    (hW : ∀ p ∈ ps, SessionWidths cert p.2.withOneTime)
    (established : ∀ p ∈ ps, (p.1.outputs cert p.2.withOneTime).getD 0 [] = [255])
    (hconv : ∀ p ∈ ps, p.2.input cert content "conversation" =
      keptConversation (p.1.outputs cert p.2.withOneTime).flatten cert)
    (hpend : ∀ p ∈ ps, p.2.input cert content "pending" = keptPending (p.1.outputs cert p.2.withOneTime).flatten cert)
    (opened : ∀ p ∈ ps, (p.2.outputs cert content).getD 0 [] = [255]) :
    ps.map (fun p => (p.2.outputs cert content).getD 3 []) = ps.map (firstOf cert content) :=
  TlsMpc.KernelSpecs.EstablishDevices.openedEnvelopes_first cert content ps hb
    (fun p hp => first_wired cert content p.1 p.2 (hW p hp) (established p hp) (hconv p hp) (hpend p hp) (opened p hp))

theorem establish_out1 {W : Type} {s : TlsMpc.Sha256.Ops (BitVec 8) W} {size : Nat}
    {checks dh1 dh2 dh3 oneTime kem ratchetAgreement basePublic ratchetPublic senderPublic identityKey signedPrekey
      certificate uuid accessKey requestId device registration localRegistration oneTimeId signedId kyberId
      ciphertext : List (BitVec 8)}
    (h : (TlsMpc.Signal.Establish.establish s TlsMpc.ByteAuth.concrete size checks dh1 dh2 dh3 oneTime kem
      ratchetAgreement basePublic ratchetPublic senderPublic identityKey signedPrekey certificate uuid accessKey requestId
      device registration localRegistration oneTimeId signedId kyberId ciphertext).getD 0 [] = [255]) :
    ∃ X, (TlsMpc.Signal.Establish.establish s TlsMpc.ByteAuth.concrete size checks dh1 dh2 dh3 oneTime kem
      ratchetAgreement basePublic ratchetPublic senderPublic identityKey signedPrekey certificate uuid accessKey requestId
      device registration localRegistration oneTimeId signedId kyberId ciphertext).getD 1 [] = certificate ++ X := by
  unfold TlsMpc.Signal.Establish.establish at h ⊢
  simp only [List.getD_cons_zero, List.getD_cons_succ, List.cons.injEq, and_true] at h ⊢
  rw [h, TlsMpc.ByteAuth.release_accept, List.append_assoc]
  exact ⟨_, rfl⟩

/-- **The stored record rebuilds the conversation**: an accepted session's conversation output is
its certificate input followed by the record the commit stores. -/
theorem stored_record (cert : Nat) (oneTime : Bool) (s : DeviceSession)
    (established : (s.outputs cert oneTime).getD 0 [] = [255]) :
    (s.outputs cert oneTime).getD 1 [] = s.input cert oneTime "certificate" ++ ((s.outputs cert oneTime).getD 1 []).drop cert := by
  have hs := TlsMpc.EstablishKernel.establishSession_spec cert oneTime s.assign
  simp only at hs
  have hl := (TlsMpc.KernelSpecs.EstablishFirst.sessionInputs_lengths cert oneTime s.assign).1
  simp only at hl
  simp only [DeviceSession.outputs, DeviceSession.input] at established ⊢
  rw [hs] at established ⊢
  obtain ⟨X, hX⟩ := establish_out1 established
  rw [hX, List.drop_left' hl]

end TlsMpc.Node.Flows.Refresh
