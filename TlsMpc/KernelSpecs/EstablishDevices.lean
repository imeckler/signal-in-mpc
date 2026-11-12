import TlsMpc.KernelSpecs.EstablishFirstMessage

/-!
# The envelopes of a send to several devices (multi-device track, part 2, without the frame)

New file; it changes no definition and no emitter imports it. It does not import
`RequestFrame.lean`; the composition with the request frame is `EstablishRequest.lean`.

A message to a contact whose devices have not answered (every device after a refresh, MULTI_DEVICE.md
sections 3 and 5) is sealed once per device by `bundle-seal`, each run with its own parameters
(one-time flag, the four counter widths) and its own input assignment; the controller frames the
opened envelopes, in device order, into one `PUT /v1/messages/{uuid}`.

PROVED (standard axioms only; no `sorry`, `native_decide`, `bv_decide`):

* `openedEnvelopes_reference`: when every device's `bundle-seal` opened status 255, the list of
  opened envelopes is, device by device, the reference PreKey sealed-sender envelope
  `EstablishSeal.envelopeOf` of that run's inputs.
* `openedEnvelopes_first`: when, in addition, every run reads the records of an accepted
  `establish-session` run (the refresh), the list is, device by device,
  `EstablishFirst.Reference.firstEnvelope` of that device's key agreements, ids and keys.
-/
namespace TlsMpc.KernelSpecs.EstablishDevices
open Std.Tactic.BVDecide
open TlsMpc TlsMpc.Signal
open TlsMpc.KernelSpecs.SealValue (Byte)
open TlsMpc.HybridKernel (lookup)

/-- One device's `bundle-seal` run: its public parameters and its input assignment. -/
structure DeviceSeal where
  withOneTime : Bool
  counterWidth : Nat
  previousWidth : Nat
  epochWidth : Nat
  indexWidth : Nat
  assign : BVExpr.Assignment

/-- The kernel's four output values (status, record, timestamp, envelope). -/
def DeviceSeal.outputs (cert content : Nat) (d : DeviceSeal) : List (List Byte) :=
  ReceiveKernel.values (BundleKernel.bundleSeal cert d.withOneTime content d.counterWidth d.previousWidth
    d.epochWidth d.indexWidth) d.assign

/-- The value of an input field of the run. -/
def DeviceSeal.input (cert content : Nat) (d : DeviceSeal) (name : String) : List Byte :=
  (lookup (BundleKernel.sealInputs cert content) name).map (BVExpr.eval d.assign)

/-- The reference envelope of the run (`EstablishSeal.envelopeOf` of its inputs). -/
def DeviceSeal.reference (cert content : Nat) (d : DeviceSeal) : List Byte :=
  let get := d.input cert content
  let record := get "conversation"
  EstablishSeal.envelopeOf d.withOneTime ⟨d.counterWidth, d.previousWidth, true⟩ ⟨d.epochWidth, d.indexWidth, 0, false⟩
    content ((record.drop cert).take 262) ((record.drop (cert + 262)).take 57) (get "pending")
    ((record.drop 0).take cert) (get "localAddress") (get "text") (get "ephemeralPublic") (get "senderPublic")
    (get "ephemeralAgreement") (get "staticAgreement")

/-- The run's public parameters are within the bound of `EstablishSeal.bundleSeal_value`. -/
def DeviceSeal.bounded (cert content : Nat) (d : DeviceSeal) : Prop :=
  cert + content + d.counterWidth + d.previousWidth + d.epochWidth + d.indexWidth < 2 ^ 30

theorem device_reference (cert content : Nat) (d : DeviceSeal) (hb : d.bounded cert content)
    (opened : (d.outputs cert content).getD 0 [] = [255]) :
    (d.outputs cert content).getD 3 [] = d.reference cert content :=
  (EstablishSeal.bundleSeal_accepted cert d.withOneTime content d.counterWidth d.previousWidth d.epochWidth
    d.indexWidth d.assign hb opened).2.2.2

/-- **Every device accepted ⇒ the opened envelopes are the reference envelopes, in order.** -/
theorem openedEnvelopes_reference (cert content : Nat) (ds : List DeviceSeal)
    (hb : ∀ d ∈ ds, d.bounded cert content)
    (opened : ∀ d ∈ ds, (d.outputs cert content).getD 0 [] = [255]) :
    ds.map (fun d => (d.outputs cert content).getD 3 []) = ds.map (fun d => d.reference cert content) :=
  List.map_congr_left (fun d hd => device_reference cert content d (hb d hd) (opened d hd))

/-- One device's establishment run (`establish-session`) during a refresh. -/
structure DeviceSession where
  assign : BVExpr.Assignment

def DeviceSession.outputs (cert : Nat) (withOneTime : Bool) (s : DeviceSession) : List (List Byte) :=
  EstablishKernel.Kernel.values (EstablishKernel.establishSession cert withOneTime) s.assign

def DeviceSession.input (cert : Nat) (withOneTime : Bool) (s : DeviceSession) (name : String) : List Byte :=
  (lookup (EstablishKernel.sessionInputs cert withOneTime) name).map (BVExpr.eval s.assign)

/-- The first envelope to a device from its establishment run and its seal run. -/
def firstOf (cert content : Nat) (p : DeviceSession × DeviceSeal) : List Byte :=
  let est := p.1.input cert p.2.withOneTime
  let sealIn := p.2.input cert content
  EstablishFirst.Reference.firstEnvelope p.2.withOneTime ⟨p.2.counterWidth, p.2.previousWidth, true⟩
    ⟨p.2.epochWidth, p.2.indexWidth, 0, false⟩ content
    (est "dh1") (est "dh2") (est "dh3") (est "dh4") (est "kemSecret") (est "ratchetAgreement")
    (est "kemCiphertext") (est "basePublic") (est "ratchetPublic") (est "senderPublic") (est "identityKey")
    (est "certificate") (est "uuid") (est "deviceId") (est "localRegistrationId") (est "oneTimePrekeyId")
    (est "signedPrekeyId") (est "kyberPrekeyId") (sealIn "localAddress") (sealIn "text")
    (sealIn "ephemeralPublic") (sealIn "senderPublic") (sealIn "ephemeralAgreement") (sealIn "staticAgreement")

/-- The seal run reads the establishment run's records, and both accepted. -/
def wired (cert content : Nat) (p : DeviceSession × DeviceSeal) : Prop :=
  (p.1.outputs cert p.2.withOneTime).getD 0 [] = [255] ∧
    p.2.input cert content "conversation" = (p.1.outputs cert p.2.withOneTime).getD 1 [] ∧
    p.2.input cert content "pending" = (p.1.outputs cert p.2.withOneTime).getD 2 [] ∧
    (p.2.outputs cert content).getD 0 [] = [255]

/-- **The first message after a refresh**: device by device, the opened envelope is the first
PreKey sealed-sender message of the session its `establish-session` run set up. -/
theorem openedEnvelopes_first (cert content : Nat) (ps : List (DeviceSession × DeviceSeal))
    (hb : ∀ p ∈ ps, p.2.bounded cert content) (hw : ∀ p ∈ ps, wired cert content p) :
    ps.map (fun p => (p.2.outputs cert content).getD 3 []) = ps.map (firstOf cert content) := by
  apply List.map_congr_left
  intro p hp
  obtain ⟨h0, h1, h2, h3⟩ := hw p hp
  exact EstablishFirst.firstMessage_envelope cert p.2.withOneTime content p.2.counterWidth p.2.previousWidth
    p.2.epochWidth p.2.indexWidth p.1.assign p.2.assign (hb p hp) h0 h1 h2 h3

#print axioms openedEnvelopes_reference
#print axioms openedEnvelopes_first

end TlsMpc.KernelSpecs.EstablishDevices
