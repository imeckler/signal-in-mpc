import TlsMpc.Node.Flows.SendProofs
import TlsMpc.Node.Flows.ContactsTable

/-!
# Op 61 / op 62 / the record seal for several devices: the composed headline (S13, F52, F58)

REORGANIZATION_PLAN.md stage S13. New file; it changes no definition. No I/O; no emitter imports
this module.

THE `bundle-seal` OUTPUT SLICING (F52, F58).
  * `bundleEnvBytes_eq` (F58): on every assignment the envelope field of `bundle-seal` has the length
    `Send.bundleEnvBytes` computes (its value function on the all-zero inputs), under the kernel's
    own parameter bound only.
  * `bundleOut_record_length`: the conversation field has `cert + min 262 (182 + content) + 57`
    bytes. So it is `cert + 319` (what `devicesScript` slices with) exactly when the padded content
    has at least 80 bytes. FINDING: for an official 89-byte text (`classes = 1`, content 79) the
    field has `cert + 318` bytes; `devicesScript`'s envelope slice then ends past the kernel's output,
    the run aborts before any status of that send is opened (the C++ `seal_devices` aborted the
    session at its `need(... "conversation shape")`, after opening the status). Fail-closed, but an
    official 89-byte text cannot be sent to an unanswered device (gap S13-10).
  * `bundleOut_lengths`: status 1, conversation `cert + 319` (content ≥ 80), timestamp 8, envelope
    `bundleEnvBytes`; `bundle_accepted_value`: on an opened status 255, the record the script keeps
    is the advanced session block with the stored metadata, and the opened timestamp ‖ envelope is
    the built text's timestamp followed by the reference PreKey sealed-sender envelope
    `EstablishSeal.envelopeOf` of exactly the script's conversation, pending block, address, text
    and words.

THE HEADLINE (`devices_accepted`, op 61 + op 62 + the request's record seal, the analogue of
`Send.send_accepted`). Device by device (`DevSend`: kind, widths, the stored record and pending
block, the four words) the script runs `signal-seal-official|built` (kind 0) or `bundle-seal`
(kinds 1, 2) on its own bundle (`DevSend.bundle`, the order `deviceSealBlock` concatenates). With
every input either the stored state, the built text, the account's address and certificate, or a
value the script opens itself: when the one opening of all statuses is all 255 and the request's
accepted byte is 255,
  * every device's status is 255 and the record kept for it is the advanced one (`DevSend.advanced`:
    `SealSend.advancedRecord` for kind 0, the advanced session block of `EstablishSeal` for kinds 1, 2);
  * the envelopes `splitEnvelopes` cuts out of the one opening of all timestamps ‖ envelopes are, in
    device order, the reference envelopes (`DevSend.reference`: `sealV1` of `SpqrSend.canonical` for
    kind 0, `EstablishSeal.envelopeOf` for kinds 1, 2), and the timestamp is the built text's;
  * the records op 62 slices out of the NEW state (at `Contacts.deviceSpans`) are the advanced
    records, in device order (`spans_records`);
  * what leaves for the server, header ‖ ciphertext ‖ tag, is `TlsRecord.sealCore` of the WebSocket
    frame of `PublicRequest.devicesMessage` holding those envelopes in device order, its slots filled
    from the advanced records.
No worker-wiring hypothesis: the frame is `buildDevices` of the script's own opened envelopes and
timestamp (`built` of `EstablishRequest.serverReceives_refresh` is gone), the kernels' inputs are the
scripts' concatenations (`hframe`, `hmask` discharged by `bundle_get`), and the pairs are the
script path's own (`devicesName_paired`).

ALL OR NOTHING. `gate_iff`: the opened statuses are all 255 exactly when every device's status is;
`devices_refused`: when some device's status is not 255, the script's continuation after the one
status opening (`afterStatuses`) is silent (no envelope of ANY device is opened: the C++ opened device
k's envelope before device k + 1's status) and returns `none` (the stored state is kept), against any
adversary (`devices_refused_view`).
-/

namespace TlsMpc.Node.Flows.Send

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts
open Std.Tactic.BVDecide
open TlsMpc TlsMpc.Signal
open TlsMpc.HybridKernel (Kernel lookup lookupFrom)

/-! ## `bundle-seal`'s output fields -/

section BundleOut

variable (cert content : Nat) (oneTime : Bool) (cw pw ew iw : Nat)

/-- `bundle-seal`'s bound on its public parameters (`EstablishSeal.bundleSeal_value`). -/
def BundleBound : Prop := cert + content + cw + pw + ew + iw < 2 ^ 30

theorem bundle_conv_length (a : BVExpr.Assignment) :
    ((lookup (BundleKernel.sealInputs cert content) "conversation").map (BVExpr.eval a)).length = convBytes cert := by
  have h : ((lookup (BundleKernel.sealInputs cert content) "conversation").map (BVExpr.eval a)).length =
      HybridKernel.conversationBytes cert 80 := by
    simp [lookup, HybridKernel.lookupFrom, BundleKernel.sealInputs, ByteCircuit.inputBytes]
  rw [h]
  unfold HybridKernel.conversationBytes convBytes recordBytes
  omega

theorem bundle_text_length (a : BVExpr.Assignment) :
    ((lookup (BundleKernel.sealInputs cert content) "text").map (BVExpr.eval a)).length = content + 10 := by
  simp [lookup, HybridKernel.lookupFrom, BundleKernel.sealInputs, ByteCircuit.inputBytes, HybridKernel.Shape.variables]

theorem bundle_zero_text :
    (lookup (BundleKernel.sealInputs cert content) "text").map (BVExpr.eval zeroA) = List.replicate (content + 10) 0 := by
  have hC : HybridKernel.conversationBytes cert 80 = convBytes cert := by
    simp [HybridKernel.conversationBytes, convBytes, recordBytes]
  rw [show lookup (BundleKernel.sealInputs cert content) "text" =
      ByteCircuit.inputBytes (convBytes cert + EstablishKernel.pendingBytes + 17) (content + 10) by
    simp [lookup, lookupFrom, BundleKernel.sealInputs, hC, HybridKernel.Shape.variables], inputBytes_zero]

/-- The record field of `EstablishSeal.sealMessageValue` when the text's validity byte is not 255
(the kernel's reject branch): 182 bytes of session block and the `size` content bytes. -/
theorem smv_reject_length (withOneTime : Bool) (shape : Serialization.Shape) (pqShape : SpqrMessage.Shape)
    (size : Nat) (session metadata pending certificate localAddress text e s ea sa : B8)
    (hs : session.length = 262) (ht : 2 + size ≤ text.length)
    (h0 : OpenResult.get ByteAuth.concrete text 0 ≠ 255) :
    ((KernelSpecs.EstablishSeal.sealMessageValue withOneTime shape pqShape size session metadata pending certificate
      localAddress text e s ea sa).getD 1 []).length = 182 + size := by
  unfold KernelSpecs.EstablishSeal.sealMessageValue
  dsimp only
  split
  · next h => exact absurd h.2.2 h0
  · simp only [List.getD_cons_succ, List.getD_cons_zero, List.length_append, List.length_cons, List.length_nil,
      KernelSpecs.EstablishSeal.inputOf, Establish.sendInput, Establish.part, List.length_take, List.length_drop, hs]
    omega

/-- **F58: `bundleEnvBytes` is the kernel's envelope length**, on every assignment. -/
theorem bundleEnvBytes_eq (a : BVExpr.Assignment) (hb : BundleBound cert content cw pw ew iw) :
    ((ReceiveKernel.values (BundleKernel.bundleSeal cert oneTime content cw pw ew iw) a).getD 3 []).length =
      bundleEnvBytes cert oneTime content cw pw ew iw := by
  have hz := KernelSpecs.EstablishSeal.bundleSeal_value cert oneTime content cw pw ew iw zeroA hb
  have l3 := values_length (BundleKernel.bundleSeal cert oneTime content cw pw ew iw) a zeroA 3
  simp only at hz
  change ((ReceiveKernel.values _ a).getD 3 []).length = ((ReceiveKernel.values _ zeroA).getD 3 []).length at l3
  rw [l3, hz]
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  rfl

/-- **The conversation field of `bundle-seal`**: `cert + min 262 (182 + content) + 57` bytes, on every
assignment (so `cert + 319` exactly when `80 ≤ content`). -/
theorem bundleOut_record_length (a : BVExpr.Assignment) (hb : BundleBound cert content cw pw ew iw) :
    ((ReceiveKernel.values (BundleKernel.bundleSeal cert oneTime content cw pw ew iw) a).getD 1 []).length =
      cert + min 262 (182 + content) + 57 := by
  have hz := KernelSpecs.EstablishSeal.bundleSeal_value cert oneTime content cw pw ew iw zeroA hb
  have l1 := values_length (BundleKernel.bundleSeal cert oneTime content cw pw ew iw) a zeroA 1
  simp only at hz
  change ((ReceiveKernel.values _ a).getD 1 []).length = ((ReceiveKernel.values _ zeroA).getD 1 []).length at l1
  rw [l1, hz]
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  have hc := bundle_conv_length cert content zeroA
  have ht0 := bundle_zero_text cert content
  have hrej : OpenResult.get ByteAuth.concrete
      ((lookup (BundleKernel.sealInputs cert content) "text").map (BVExpr.eval zeroA)) 0 ≠ 255 := by
    rw [ht0]
    simp [OpenResult.get]
  have hs262 : (((lookup (BundleKernel.sealInputs cert content) "conversation").map (BVExpr.eval zeroA)).drop cert
      |>.take 262).length = 262 := by
    simp only [List.length_take, List.length_drop, hc, convBytes, recordBytes]
    omega
  have ht2 : 2 + content ≤ ((lookup (BundleKernel.sealInputs cert content) "text").map (BVExpr.eval zeroA)).length := by
    rw [bundle_text_length]
    omega
  rw [List.length_append, List.length_append, List.length_take (i := 262),
    smv_reject_length _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs262 ht2 hrej]
  simp only [List.length_take, List.length_drop, hc, convBytes, recordBytes]
  omega

/-- **`bundle-seal`'s output lengths**: status 1, conversation `cert + 319`, timestamp 8, envelope
`bundleEnvBytes` (four fields), on every assignment, when the padded content has at least 80 bytes. -/
theorem bundleOut_lengths (a : BVExpr.Assignment) (hb : BundleBound cert content cw pw ew iw) (h80 : 80 ≤ content) :
    let o := ReceiveKernel.values (BundleKernel.bundleSeal cert oneTime content cw pw ew iw) a
    (o.getD 0 []).length = 1 ∧ (o.getD 1 []).length = convBytes cert ∧ (o.getD 2 []).length = 8 ∧
      (o.getD 3 []).length = bundleEnvBytes cert oneTime content cw pw ew iw ∧ o.length = 4 := by
  intro o
  have hv := KernelSpecs.EstablishSeal.bundleSeal_value cert oneTime content cw pw ew iw a hb
  simp only at hv
  refine ⟨?_, ?_, ?_, bundleEnvBytes_eq cert content oneTime cw pw ew iw a hb, ?_⟩
  · show ((ReceiveKernel.values _ a).getD 0 []).length = 1
    rw [hv]
    simp only [List.getD_cons_zero]
    unfold KernelSpecs.EstablishSeal.sealMessageValue
    dsimp only
    split <;> rfl
  · show ((ReceiveKernel.values _ a).getD 1 []).length = _
    rw [bundleOut_record_length cert content oneTime cw pw ew iw a hb]
    simp only [convBytes, recordBytes]
    omega
  · show ((ReceiveKernel.values _ a).getD 2 []).length = 8
    rw [hv]
    simp only [List.getD_cons_succ, List.getD_cons_zero, List.length_take, List.length_drop, bundle_text_length]
    omega
  · show (List.map _ (BundleKernel.bundleSeal cert oneTime content cw pw ew iw).outputs).length = 4
    rw [List.length_map]
    rfl

/-- **An accepted `bundle-seal` run, as `devicesScript` slices and opens it.** For the bundle the
script builds for a device of kind 1 or 2 (certificate ‖ record, pending block, our address, the
built text, four words): when the opened status byte is 255, the reference send step accepts the
session block; the record the script keeps (`recordFrom … recordEnd`) is the advanced session block
with the stored metadata; the opened timestamp ‖ envelope (`recordEnd … envelopeEnd`) is the built
text's timestamp followed by the reference PreKey sealed-sender envelope `EstablishSeal.envelopeOf` of
the script's conversation, pending block, address, text and words. -/
theorem bundle_accepted_value (conv pending address text : B8) (w : Bits) (hc : conv.length = convBytes cert)
    (hp : pending.length = EstablishKernel.pendingBytes) (ha : address.length = 17) (ht : text.length = content + 10)
    (hb : BundleBound cert content cw pw ew iw) (h80 : 80 ≤ content) :
    let K := BundleKernel.bundleSeal cert oneTime content cw pw ew iw
    let v := bitsOf conv ++ (bitsOf pending ++ (bitsOf address ++ (bitsOf text ++ w)))
    let a := shapedAssign K.inputs v
    let get := fun name => (lookup (BundleKernel.sealInputs cert content) name).map (BVExpr.eval a)
    let out := shapedOut K v
    out.take 1 = [255] →
    let session := (conv.drop cert).take 262
    let metadata := (conv.drop (cert + 262)).take 57
    let shape : Serialization.Shape := ⟨cw, pw, true⟩
    let pqShape : SpqrMessage.Shape := ⟨ew, iw, 0, false⟩
    let i := KernelSpecs.EstablishSeal.inputOf content session metadata address text
    let p := SpqrSend.canonical shape pqShape i
    SpqrSend.accepted shape pqShape i ∧
    (out.drop (1 + cert)).take recordBytes =
      (session.take 1 ++ p.nextCounter ++ Establish.part session 5 36 ++ p.nextChainKey ++ p.nextPqChainKey ++
        p.nextPqCounter ++ Establish.part session 109 8 ++ [OpenResult.get ByteAuth.concrete text 1] ++
        Establish.part session 118 64 ++ Establish.part text 2 content).take 262 ++ metadata ∧
    (out.drop (1 + convBytes cert)).take (8 + bundleEnvBytes cert oneTime content cw pw ew iw) =
      (text.drop (2 + content)).take 8 ++
        KernelSpecs.EstablishSeal.envelopeOf oneTime shape pqShape content session metadata pending (conv.take cert)
          address text (get "ephemeralPublic") (get "senderPublic") (get "ephemeralAgreement") (get "staticAgreement") := by
  intro K v a get out hst session metadata shape pqShape i p
  obtain ⟨-, g1, g2, g3, g4⟩ := bundleSeal_get cert content conv pending address text w hc hp ha ht oneTime cw pw ew iw
  change (lookup (BundleKernel.sealInputs cert content) "conversation").map (BVExpr.eval a) = conv at g1
  change (lookup (BundleKernel.sealInputs cert content) "pending").map (BVExpr.eval a) = pending at g2
  change (lookup (BundleKernel.sealInputs cert content) "localAddress").map (BVExpr.eval a) = address at g3
  change (lookup (BundleKernel.sealInputs cert content) "text").map (BVExpr.eval a) = text at g4
  obtain ⟨L0, L1, L2, L3, L4⟩ := bundleOut_lengths cert content oneTime cw pw ew iw a hb h80
  have hout : out = (ReceiveKernel.values K a).flatten := rfl
  rw [flatten4 _ L4] at hout
  obtain ⟨s0, s1, s2⟩ := slice4 _ _ _ _ cert _ L0 (by rw [L1]; rfl) L2 L3
  rw [← hout] at s0 s1 s2
  rw [hst] at s0
  have hv := KernelSpecs.EstablishSeal.bundleSeal_value cert oneTime content cw pw ew iw a hb
  simp only at hv
  change ReceiveKernel.values K a = _ at hv
  rw [g1, g2, g3, g4] at hv
  rw [hv] at s0 s1 s2
  simp only [List.getD_cons_succ, List.getD_cons_zero] at s0 s1 s2
  have facts := KernelSpecs.EstablishSeal.sealMessageValue_accepted _ _ _ _ _ _ _ _ _ _ _ _ _ _ s0.symm
  simp only at facts
  obtain ⟨hA, -, -, h1, h2⟩ := facts
  have hcl : ((conv.drop 0).take cert).length = cert := by
    simp only [List.drop_zero, List.length_take, hc, convBytes]; omega
  refine ⟨hA, ?_, ?_⟩
  · rw [s1, List.append_assoc, List.drop_left' hcl, h1]
  · rw [show convBytes cert = cert + recordBytes from rfl, s2, h2]
    simp only [List.drop_zero]
    rfl

end BundleOut

/-! ## Op 61 at the value level: devices in order -/

/-- What every device of one op-61 send shares: the certificate (length and bytes), the text's size
class, the built text and our own address. -/
structure DevCtx where
  cert : Nat
  classes : Nat
  official : Bool
  certB : B8
  text : B8
  address : B8

/-- The padded content length (`SealFixed.contentBytes`). -/
def DevCtx.content (c : DevCtx) : Nat := KernelSpecs.SealFixed.contentBytes c.classes c.official

/-- The built text's timestamp (`text[2 + content ..]`, 8 bytes). -/
def DevCtx.timestamp (c : DevCtx) : B8 := (c.text.drop (2 + c.content)).take 8

structure DevCtx.Ok (c : DevCtx) : Prop where
  cert : c.certB.length = c.cert
  text : c.text.length = textBytes c.classes c.official
  classes : 1 ≤ c.classes

/-- One device of op 61 at the value level: its kind, the widths read from its flags, its stored
record and pending block (slices of the stored state at `Contacts.deviceSpans`), and the four words
its kernel reads (ephemeral public key, sender key, ephemeral agreement, static agreement). -/
structure DevSend where
  kind : Nat
  cw : Nat
  pw : Nat
  ew : Nat
  iw : Nat
  record : B8
  pending : B8
  words : Bits

namespace DevSend

variable (c : DevCtx) (d : DevSend)

/-- The kernel the script names for the device (`deviceKernel`). -/
def kernel : Kernel :=
  if d.kind = 0 then sealK c.cert d.cw d.pw d.ew d.iw c.classes c.official
  else BundleKernel.bundleSeal c.cert (d.kind == 2) (bundleContent c.classes c.official) d.cw d.pw d.ew d.iw

/-- The device's input bundle in the order `deviceSealBlock` concatenates it. -/
def bundle : Bits :=
  if d.kind = 0 then bitsOf (c.certB ++ d.record) ++ (bitsOf c.text ++ d.words)
  else bitsOf (c.certB ++ d.record) ++ (bitsOf d.pending ++ (bitsOf c.address ++ (bitsOf c.text ++ d.words)))

/-- The kernel's output on the device's bundle (status ‖ conversation ‖ timestamp ‖ envelope). -/
def out : B8 := shapedOut (d.kernel c) (d.bundle c)

/-- The envelope length the script slices with (`deviceKernel`'s second component). -/
def env : Nat :=
  if d.kind = 0 then sealEnvBytes c.cert c.classes c.official d.cw d.pw d.ew d.iw
  else bundleEnvBytes c.cert (d.kind == 2) (bundleContent c.classes c.official) d.cw d.pw d.ew d.iw

/-- The script's status slice (`0 … statusEnd`). -/
def status : B8 := (d.out c).take 1

/-- The record the script keeps (`recordFrom … recordEnd`). -/
def kept : B8 := ((d.out c).drop (1 + c.cert)).take recordBytes

/-- The timestamp ‖ envelope the script opens (`recordEnd … envelopeEnd`). -/
def sealed : B8 := ((d.out c).drop (1 + convBytes c.cert)).take (8 + d.env c)

/-- The reference envelope of the device's message: `sealV1` of the reference Signal message for kind
0 (`seal_accepted_value`), the reference PreKey sealed-sender envelope `EstablishSeal.envelopeOf` for
kinds 1, 2 (`bundle_accepted_value`). The four words as the kernel reads them. -/
def reference : B8 :=
  let a := shapedAssign (d.kernel c).inputs (d.bundle c)
  let conv := c.certB ++ d.record
  if d.kind = 0 then
    let get := fun name => (lookup (KernelSpecs.SealFixed.sealInputs c.cert c.classes c.official) name).map
      (BVExpr.eval a)
    let staged := KernelSpecs.SealFixed.stagedOf ((conv.drop c.cert).take (182 + 80)) c.text
    let i := KernelSpecs.SealFixed.inputOf 0 staged c.text (KernelSpecs.SealFixed.contentBytes c.classes c.official)
    KernelSpecs.SealValue.Reference.sealV1 i.receiver (get "ephemeralPublic") (get "senderPublic")
      (get "ephemeralAgreement") (get "staticAgreement") c.certB
      (SpqrSend.canonical ⟨d.cw, d.pw, false⟩ ⟨d.ew, d.iw, 1, false⟩ i).wire
  else
    let content := bundleContent c.classes c.official
    let get := fun name => (lookup (BundleKernel.sealInputs c.cert content) name).map (BVExpr.eval a)
    let session := (conv.drop c.cert).take 262
    let metadata := (conv.drop (c.cert + 262)).take 57
    KernelSpecs.EstablishSeal.envelopeOf (d.kind == 2) ⟨d.cw, d.pw, true⟩ ⟨d.ew, d.iw, 0, false⟩ content session
      metadata d.pending c.certB c.address c.text (get "ephemeralPublic") (get "senderPublic")
      (get "ephemeralAgreement") (get "staticAgreement")

/-- The advanced record (without the certificate): `SealSend.advancedRecord` for kind 0, the
advanced session block with the stored metadata for kinds 1, 2. -/
def advanced : B8 :=
  let conv := c.certB ++ d.record
  if d.kind = 0 then
    let staged := KernelSpecs.SealFixed.stagedOf ((conv.drop c.cert).take (182 + 80)) c.text
    let i := KernelSpecs.SealFixed.inputOf 0 staged c.text (KernelSpecs.SealFixed.contentBytes c.classes c.official)
    (KernelSpecs.SealSend.advancedRecord c.cert conv staged
      (SpqrSend.canonical ⟨d.cw, d.pw, false⟩ ⟨d.ew, d.iw, 1, false⟩ i)).drop c.cert
  else
    let content := bundleContent c.classes c.official
    let session := (conv.drop c.cert).take 262
    let metadata := (conv.drop (c.cert + 262)).take 57
    let p := SpqrSend.canonical ⟨d.cw, d.pw, true⟩ ⟨d.ew, d.iw, 0, false⟩
      (KernelSpecs.EstablishSeal.inputOf content session metadata c.address c.text)
    (session.take 1 ++ p.nextCounter ++ Establish.part session 5 36 ++ p.nextChainKey ++ p.nextPqChainKey ++
      p.nextPqCounter ++ Establish.part session 109 8 ++ [OpenResult.get ByteAuth.concrete c.text 1] ++
      Establish.part session 118 64 ++ Establish.part c.text 2 content).take 262 ++ metadata

end DevSend

/-- What the device needs (from the stored state and the kernels' public bounds). -/
structure DevSend.Ok (c : DevCtx) (d : DevSend) : Prop where
  record : d.record.length = recordBytes
  sealOk : d.kind = 0 → SealBound c.cert d.cw d.pw d.ew d.iw c.classes c.official
  bundleOk : d.kind ≠ 0 → d.pending.length = EstablishKernel.pendingBytes ∧ c.address.length = 17 ∧
    80 ≤ bundleContent c.classes c.official ∧ BundleBound c.cert (bundleContent c.classes c.official) d.cw d.pw d.ew d.iw

theorem bundleContent_eq (classes : Nat) (official : Bool) :
    bundleContent classes official = KernelSpecs.SealFixed.contentBytes classes official := by
  cases official <;>
    simp [bundleContent, KernelSpecs.SealFixed.contentBytes, PrivateTextNotification.officialPaddedBytes,
      PrivateTextNotification.paddedBytes]

theorem DevCtx.timestamp_length (c : DevCtx) (hc : c.Ok) : c.timestamp.length = 8 := by
  obtain ⟨hT, -⟩ := textBytes_eq c.classes c.official hc.classes
  simp only [DevCtx.timestamp, DevCtx.content, List.length_take, List.length_drop, hc.text, hT]
  omega

/-- The kernel's whole output length on the device's bundle. -/
theorem DevSend.out_length (c : DevCtx) (d : DevSend) (hc : c.Ok) (hd : d.Ok c) :
    (d.out c).length = 1 + convBytes c.cert + (8 + d.env c) := by
  by_cases h0 : d.kind = 0
  · obtain ⟨L0, L1, L2, L3, L4⟩ := sealOut_lengths c.cert d.cw d.pw d.ew d.iw c.classes c.official
      (shapedAssign (sealK c.cert d.cw d.pw d.ew d.iw c.classes c.official).inputs
        (bitsOf (c.certB ++ d.record) ++ (bitsOf c.text ++ d.words))) (hd.sealOk h0) hc.classes
    have e : d.out c = ((sealK c.cert d.cw d.pw d.ew d.iw c.classes c.official).outputs.map (fun f => f.value.map
        (BVExpr.eval (shapedAssign (sealK c.cert d.cw d.pw d.ew d.iw c.classes c.official).inputs
          (bitsOf (c.certB ++ d.record) ++ (bitsOf c.text ++ d.words)))))).flatten := by
      simp only [DevSend.out, DevSend.kernel, DevSend.bundle, if_pos h0]
      rfl
    rw [e, flatten4 _ L4]
    simp only [List.length_append, L0, L1, L2, L3, DevSend.env, if_pos h0]
    omega
  · obtain ⟨-, -, h80, hb⟩ := hd.bundleOk h0
    obtain ⟨L0, L1, L2, L3, L4⟩ := bundleOut_lengths c.cert (bundleContent c.classes c.official) (d.kind == 2)
      d.cw d.pw d.ew d.iw (shapedAssign (BundleKernel.bundleSeal c.cert (d.kind == 2) (bundleContent c.classes c.official)
        d.cw d.pw d.ew d.iw).inputs (bitsOf (c.certB ++ d.record) ++ (bitsOf d.pending ++ (bitsOf c.address ++
          (bitsOf c.text ++ d.words))))) hb h80
    have e : d.out c = (ReceiveKernel.values (BundleKernel.bundleSeal c.cert (d.kind == 2)
        (bundleContent c.classes c.official) d.cw d.pw d.ew d.iw)
        (shapedAssign (BundleKernel.bundleSeal c.cert (d.kind == 2) (bundleContent c.classes c.official)
          d.cw d.pw d.ew d.iw).inputs (bitsOf (c.certB ++ d.record) ++ (bitsOf d.pending ++ (bitsOf c.address ++
            (bitsOf c.text ++ d.words)))))).flatten := by
      simp only [DevSend.out, DevSend.kernel, DevSend.bundle, if_neg h0]
      rfl
    rw [e, flatten4 _ L4]
    simp only [List.length_append, L0, L1, L2, L3, DevSend.env, if_neg h0]
    omega

theorem DevSend.status_length (c : DevCtx) (d : DevSend) (hc : c.Ok) (hd : d.Ok c) : (d.status c).length = 1 := by
  simp only [DevSend.status, List.length_take, DevSend.out_length c d hc hd]
  omega

theorem DevSend.kept_length (c : DevCtx) (d : DevSend) (hc : c.Ok) (hd : d.Ok c) : (d.kept c).length = recordBytes := by
  simp only [DevSend.kept, List.length_take, List.length_drop, DevSend.out_length c d hc hd, convBytes]
  omega

theorem DevSend.sealed_length (c : DevCtx) (d : DevSend) (hc : c.Ok) (hd : d.Ok c) :
    (d.sealed c).length = 8 + d.env c := by
  simp only [DevSend.sealed, List.length_take, List.length_drop, DevSend.out_length c d hc hd]
  omega

/-- **One accepted device**: the record the script keeps is the advanced one and the opened
timestamp ‖ envelope is the built text's timestamp and the reference envelope. -/
theorem DevSend.accepted (c : DevCtx) (d : DevSend) (hc : c.Ok) (hd : d.Ok c) (hst : d.status c = [255]) :
    d.kept c = d.advanced c ∧ d.sealed c = c.timestamp ++ d.reference c := by
  have hconv : (c.certB ++ d.record).length = convBytes c.cert := by
    simp [hc.cert, hd.record, convBytes]
  have hct : (c.certB ++ d.record).take c.cert = c.certB := List.take_left' hc.cert
  by_cases h0 : d.kind = 0
  · have hout : d.out c = shapedOut (sealK c.cert d.cw d.pw d.ew d.iw c.classes c.official)
        (bitsOf (c.certB ++ d.record) ++ (bitsOf c.text ++ d.words)) := by
      simp only [DevSend.out, DevSend.kernel, DevSend.bundle, if_pos h0]
    have hst' : (shapedOut (sealK c.cert d.cw d.pw d.ew d.iw c.classes c.official)
        (bitsOf (c.certB ++ d.record) ++ (bitsOf c.text ++ d.words))).take 1 = [255] := by
      rw [← hout]; exact hst
    obtain ⟨-, -, hrec, hte⟩ := seal_accepted_value c.cert d.cw d.pw d.ew d.iw c.classes c.official
      (c.certB ++ d.record) c.text d.words hconv hc.text (hd.sealOk h0) hc.classes hst'
    rw [hct] at hrec hte
    constructor
    · show ((d.out c).drop (1 + c.cert)).take recordBytes = d.advanced c
      rw [hout]
      simp only [DevSend.advanced, if_pos h0]
      rw [← hrec, List.drop_left' hc.cert]
    · show ((d.out c).drop (1 + convBytes c.cert)).take (8 + d.env c) = _
      rw [hout]
      simp only [DevSend.env, DevSend.reference, DevSend.kernel, DevSend.bundle, if_pos h0]
      exact hte
  · obtain ⟨hp, ha, h80, hb⟩ := hd.bundleOk h0
    have hT : c.text.length = bundleContent c.classes c.official + 10 := by
      rw [hc.text, bundleContent_eq]
      exact (textBytes_eq c.classes c.official hc.classes).1
    have hout : d.out c = shapedOut (BundleKernel.bundleSeal c.cert (d.kind == 2) (bundleContent c.classes c.official)
        d.cw d.pw d.ew d.iw)
        (bitsOf (c.certB ++ d.record) ++ (bitsOf d.pending ++ (bitsOf c.address ++ (bitsOf c.text ++ d.words)))) := by
      simp only [DevSend.out, DevSend.kernel, DevSend.bundle, if_neg h0]
    have hst' : (shapedOut (BundleKernel.bundleSeal c.cert (d.kind == 2) (bundleContent c.classes c.official)
        d.cw d.pw d.ew d.iw)
        (bitsOf (c.certB ++ d.record) ++ (bitsOf d.pending ++ (bitsOf c.address ++ (bitsOf c.text ++ d.words))))).take 1 =
        [255] := by
      rw [← hout]; exact hst
    obtain ⟨-, hrec, hte⟩ := bundle_accepted_value c.cert (bundleContent c.classes c.official) (d.kind == 2)
      d.cw d.pw d.ew d.iw (c.certB ++ d.record) d.pending c.address c.text d.words hconv hp ha hT hb h80 hst'
    rw [hct] at hte
    have ets : (c.text.drop (2 + bundleContent c.classes c.official)).take 8 = c.timestamp := by
      rw [bundleContent_eq]; rfl
    rw [ets] at hte
    constructor
    · show ((d.out c).drop (1 + c.cert)).take recordBytes = d.advanced c
      rw [hout]
      simp only [DevSend.advanced, if_neg h0]
      exact hrec
    · show ((d.out c).drop (1 + convBytes c.cert)).take (8 + d.env c) = _
      rw [hout]
      simp only [DevSend.env, DevSend.reference, DevSend.kernel, DevSend.bundle, if_neg h0]
      exact hte

/-! ## The gate, the split of the opened envelopes, the request's records -/

/-- **The gate**: one-byte statuses concatenate to all 255 exactly when each is `[255]`. -/
theorem gate_iff : ∀ (ss : List B8), (∀ s ∈ ss, s.length = 1) →
    (ss.flatten = List.replicate ss.length 255 ↔ ∀ s ∈ ss, s = [255])
  | [], _ => by simp
  | s :: ss, h => by
    have ih := gate_iff ss (fun t ht => h t (by simp [ht]))
    have hs := h s (by simp)
    match s with
    | [] => exact absurd hs (by simp)
    | _ :: _ :: _ => exact absurd hs (by simp)
    | [x] =>
      simp only [List.flatten_cons, List.length_cons, List.replicate_succ, List.singleton_append, List.cons.injEq,
        ih, List.mem_cons, forall_eq_or_imp, and_true]

/-- In bits (the script compares the opened bits with `bitsOf (replicate m 255)`). -/
theorem gate_bits (ss : List B8) (h : ∀ s ∈ ss, s.length = 1) :
    bitsOf ss.flatten = bitsOf (List.replicate ss.length 255) ↔ ∀ s ∈ ss, s = [255] :=
  ⟨fun e => (gate_iff ss h).mp (bitsOf_inj _ _ e), fun e => by rw [(gate_iff ss h).mpr e]⟩

/-- **The split**: `splitEnvelopes` of the envelope lengths cuts the concatenated timestamps ‖
envelopes back into the devices' pairs. -/
theorem splitEnvelopes_flatten : ∀ (ps : List (B8 × B8)), (∀ p ∈ ps, p.1.length = 8) →
    splitEnvelopes (ps.map (·.2.length)) (ps.map (fun p => p.1 ++ p.2)).flatten = ps
  | [], _ => rfl
  | (t, v) :: ps, h => by
    have ht : t.length = 8 := h (t, v) (by simp)
    have ih := splitEnvelopes_flatten ps (fun p hp => h p (by simp [hp]))
    rw [List.map_cons, List.map_cons, List.flatten_cons]
    generalize hR : (ps.map (fun p => p.1 ++ p.2)).flatten = R at ih ⊢
    have e1 : ((t ++ v) ++ R).take 8 = t := by rw [List.append_assoc, List.take_left' ht]
    have e2 : (((t ++ v) ++ R).drop 8).take v.length = v := by
      rw [List.append_assoc, List.drop_left' ht, List.take_left' rfl]
    have e3 : ((t ++ v) ++ R).drop (8 + v.length) = R := List.drop_left' (by simp [ht])
    show splitEnvelopes (v.length :: ps.map (·.2.length)) ((t ++ v) ++ R) = (t, v) :: ps
    simp only [splitEnvelopes]
    rw [e1, e2, e3, ih]

/-- **Op 62 reads the new records**: the slices `requestDevicesScript` takes at the devices' spans
(`Contacts.deviceSpans` of the kinds) of a state laid out as record ‖ pending per device are the
records, in order. -/
theorem spans_records (f : DevSend → B8) : ∀ (ds : List DevSend) (pre : B8),
    (∀ d ∈ ds, (f d).length = recordBytes ∧ (d.kind ≠ 0 → d.pending.length = EstablishKernel.pendingBytes)) →
    ((deviceSpans pre.length (ds.map (·.kind))).map fun s =>
      ((pre ++ (ds.map fun d => f d ++ (if d.kind = 0 then [] else d.pending)).flatten).drop s.1.1).take
        recordBytes).flatten = (ds.map f).flatten
  | [], _, _ => rfl
  | d :: ds, pre, h => by
    obtain ⟨hf, hp⟩ := h d (by simp)
    have hrest : ∀ e ∈ ds, (f e).length = recordBytes ∧ (e.kind ≠ 0 → e.pending.length = EstablishKernel.pendingBytes) :=
      fun e he => h e (by simp [he])
    have ihR := spans_records f ds
    simp only [List.map_cons, List.flatten_cons]
    generalize hR : (ds.map fun d => f d ++ (if d.kind = 0 then [] else d.pending)).flatten = R at ihR ⊢
    by_cases h0 : d.kind = 0
    · have hspan : deviceSpans pre.length (d.kind :: ds.map (·.kind)) =
          ((pre.length, 319), none) :: deviceSpans (pre ++ f d).length (ds.map (·.kind)) := by
        rw [deviceSpans, if_pos h0, List.length_append, hf]
        rfl
      have ih := ihR (pre ++ f d) hrest
      rw [List.append_assoc] at ih
      show ((deviceSpans pre.length (d.kind :: ds.map (·.kind))).map fun s =>
        ((pre ++ ((f d ++ (if d.kind = 0 then [] else d.pending)) ++ R)).drop s.1.1).take recordBytes).flatten =
          f d ++ (ds.map f).flatten
      rw [hspan, if_pos h0, List.append_nil, List.map_cons, List.flatten_cons, ih]
      simp only
      rw [List.drop_left, List.take_left' hf]
    · have hpl := hp h0
      have hspan : deviceSpans pre.length (d.kind :: ds.map (·.kind)) =
          ((pre.length, 319), some (pre.length + 319, 1616)) ::
            deviceSpans (pre ++ (f d ++ d.pending)).length (ds.map (·.kind)) := by
        rw [deviceSpans, if_neg h0, List.length_append, List.length_append, hf, hpl]
        rfl
      have ih := ihR (pre ++ (f d ++ d.pending)) hrest
      rw [List.append_assoc] at ih
      show ((deviceSpans pre.length (d.kind :: ds.map (·.kind))).map fun s =>
        ((pre ++ ((f d ++ (if d.kind = 0 then [] else d.pending)) ++ R)).drop s.1.1).take recordBytes).flatten =
          f d ++ (ds.map f).flatten
      rw [hspan, if_neg h0, List.map_cons, List.flatten_cons, ih]
      simp only
      rw [List.drop_left, List.append_assoc, List.take_left' hf]

/-! ## The request: `bundle-request-ctr`, then the tag -/

/-- `buildDevices` with `pairs` gives one slot pair per envelope. -/
theorem devices_length (envs : List B8) (ts id : Nat) (mask frame : B8) (official : Bool) (payloadAt : Nat)
    (offsets : List Nat) (hb : PublicRequest.buildDevices envs ts id mask official = .ok (frame, payloadAt, offsets))
    (devices : List (Nat × Nat)) (hp : BundleKernel.pairs (offsets.drop 2) = some devices) :
    devices.length = envs.length := by
  rw [KernelSpecs.RequestFrame.buildDevices_eq] at hb
  split at hb
  · cases hb
  · obtain ⟨-, -, -, -, -, ho⟩ := KernelSpecs.RequestFrame.assemble_ok _ mask frame _ payloadAt offsets hb
    have hl : offsets.length = 2 + 2 * envs.length := by
      rw [ho]; simp [KernelSpecs.RequestFrame.offsetsFold_size]
    rw [KernelSpecs.RequestFrame.pairs_spec _ devices hp]
    simp only [List.length_map, List.length_range, List.length_drop, hl]
    omega

/-- The plaintext `bundle-request-ctr` encrypts has the frame's length. -/
theorem bundlePlain_length (envs : List B8) (ts id : Nat) (mask frame : B8) (official : Bool)
    (payloadAt : Nat) (offsets : List Nat)
    (hb : PublicRequest.buildDevices envs ts id mask official = .ok (frame, payloadAt, offsets))
    (devices : List (Nat × Nat)) (hp : BundleKernel.pairs (offsets.drop 2) = some devices)
    (K seqB records : B8) (hK : K.length = 60) (hs : seqB.length = 8)
    (hr : records.length = recordBytes * devices.length) :
    let msg := PublicRequest.devicesMessage envs ts id official
    (KernelSpecs.RequestFrame.assembleHeader (PublicRequest.total msg) mask ++
      KernelSpecs.RequestFrame.maskFrom mask 0
        (KernelSpecs.RequestFrame.render (KernelSpecs.RequestFrame.devicesValues records) msg)).length = frame.length := by
  intro msg
  have hm : mask.length = 4 := by
    have hb' := hb
    rw [KernelSpecs.RequestFrame.buildDevices_eq] at hb'
    split at hb'
    · cases hb'
    · exact (KernelSpecs.RequestFrame.assemble_ok _ mask frame _ payloadAt offsets hb').2.2.1
  have h1 := bundleRequestCtr_value envs ts id mask frame official payloadAt offsets hb devices hp K seqB records hK hs hr
  have h2 := KernelSpecs.bundleRequestCtr_spec frame.length payloadAt (offsets.getD 0 0) (offsets.getD 1 0) devices
    (assignOf (requestIn K seqB records frame mask))
  obtain ⟨g1, g2, g3, g4, g5⟩ := bundle_get devices.length K seqB records frame mask hK hs hr hm
  simp only at h1 h2 g1 g2 g3 g4 g5
  rw [h1, g1, g2, g4, g5] at h2
  have h3 := congrArg (fun l => (l.getD 2 []).length) h2
  simp only [KernelSpecs.sealedRequest, List.getD_cons_succ, List.getD_cons_zero, ByteAuth.release,
    List.length_map, HybridKernel.ctrOf_length _ _ _ hK, Tls.inner_length, Tls.innerLength,
    KernelSpecs.insertSlots, List.length_zipIdx] at h3
  simp only [msg, List.length_append, KernelSpecs.RequestFrame.maskFrom_length] at h3 ⊢
  omega

/-- **The record of an accepted request** (the tail of `send_accepted`, for any request kernel whose
outputs are `sealedRequest` of a plaintext of the frame's length): header ‖ ciphertext and the tag over
the pad and both parties' halves is `TlsRecord.sealCore` of the plaintext. -/
theorem sealed_record (K seqB P : B8) (valid : BitVec 8) (hK : K.length = 60) (L : Nat) (hPl : P.length = L)
    (a b : List Tls.W) (nPow : Nat) (hsh : Local.Ghash.Shared a b (HybridKernel.hashKeyOf K) nPow)
    (hn : Local.Ghash.needed 5 (innerOf L) ≤ nPow) (ctr : B8)
    (hctr : ctr = (KernelSpecs.sealedRequest K seqB P valid).flatten) (hacc : ctr.take 1 = [255]) :
    let hc := (ctr.drop 1).take (5 + innerOf L)
    let pad := (ctr.drop (1 + 5 + innerOf L)).take 16
    let hA := Local.Ghash.toBytes (Local.Ghash.half a (hc.take 5) (hc.drop 5))
    let hB := Local.Ghash.toBytes (Local.Ghash.half b (hc.take 5) (hc.drop 5))
    hc ++ kernelOut HybridKernel.gcmTag (pad ++ (hA ++ hB)) =
      TlsRecord.sealCore Gcm.concrete ((K.drop 32).take 16) ((K.drop 48).take 12) seqB P 23 0 := by
  subst hPl
  intro hc pad hA hB
  have hH := Tls.header_length ((TlsRecord.inner Gcm.concrete P 23 0).length + 16)
  have hI : (TlsRecord.inner Gcm.concrete P 23 0).length = innerOf P.length := by
    rw [Tls.inner_length]; rfl
  have hCT : ∀ m, (ByteAuth.release ByteAuth.concrete m
      (HybridKernel.ctrOf K seqB (TlsRecord.inner Gcm.concrete P 23 0))).length = innerOf P.length := by
    intro m
    simp only [ByteAuth.release, List.length_map, HybridKernel.ctrOf_length _ _ _ hK, hI]
  have hflat : ctr = [valid] ++ (TlsRecord.header Gcm.concrete ((TlsRecord.inner Gcm.concrete P 23 0).length + 16) ++
      (ByteAuth.release ByteAuth.concrete valid (HybridKernel.ctrOf K seqB (TlsRecord.inner Gcm.concrete P 23 0)) ++
        HybridKernel.padOf K seqB)) := by
    rw [hctr]; simp [KernelSpecs.sealedRequest]
  have hv255 : valid = 255 := by
    have := hacc
    rw [hflat] at this
    simpa using this
  subst hv255
  have hP16 := Tls.padOf_length K seqB hK
  have ehc : hc = (KernelSpecs.sealedRequest K seqB P 255).getD 1 [] ++
      (KernelSpecs.sealedRequest K seqB P 255).getD 2 [] := by
    show (ctr.drop 1).take (5 + innerOf P.length) = _
    rw [hflat, List.singleton_append, List.drop_succ_cons, List.drop_zero, ← List.append_assoc,
      List.take_left' (by rw [List.length_append, hH, hCT 255])]
    simp [KernelSpecs.sealedRequest]
  have epad : pad = (KernelSpecs.sealedRequest K seqB P 255).getD 3 [] := by
    show (ctr.drop (1 + 5 + innerOf P.length)).take 16 = _
    rw [hflat, ← List.append_assoc, ← List.append_assoc,
      List.drop_left' (by rw [List.length_append, List.length_append, hH, hCT 255]; rfl),
      List.take_of_length_le (by omega)]
    simp [KernelSpecs.sealedRequest]
  have hrecord := request_record K seqB P hK a b nPow hsh hn
  simp only at hrecord
  rw [← ehc, ← epad] at hrecord
  exact hrecord

theorem sum_map_const' (ds : List DevSend) (k : Nat) : (ds.map (fun _ => k)).sum = k * ds.length := by
  induction ds with
  | nil => simp
  | cons d ds ih => simp [ih, Nat.mul_succ, Nat.add_comm]

/-! ## The headline -/

/-- **T4-SEND / T7 for several devices on the script path** (op 61, then op 62, then the request's
record seal: `bundle-request-ctr` and S12's tag). Every input is the stored state (each device's
record and pending block), the built text, the account's certificate and address, the words the
script feeds (S11's, E4), the traffic block and sequence, the parties' GHASH key-power shares; the
statuses, the timestamps ‖ envelopes and the request's accepted byte are the script's own openings
of its own slices; the frame is `buildDevices` of the envelopes `splitEnvelopes` cut out of that
opening; the records `bundle-request-ctr` reads are op 62's slices of the NEW state. So none of
`built`, `hframe`, `hmask`, `paired` of `EstablishRequest.serverReceives_refresh` is a hypothesis.

When the one status opening is all 255 and the request's accepted byte is 255: every device's
status is 255 and the record kept for it is the advanced one; the envelopes are, in device order,
the reference envelopes and the timestamp the built text's; op 62 reads the advanced records; and
what leaves for the server is the AES-GCM TLS record of the WebSocket frame of
`PublicRequest.devicesMessage` holding the reference envelopes in device order, its slots filled from
the advanced records. -/
theorem devices_accepted (c : DevCtx) (ds : List DevSend) (hc : c.Ok) (hd : ∀ d ∈ ds, d.Ok c) (hne : ds ≠ [])
    (id : Nat) (mask frame : B8) (payloadAt : Nat) (offsets : List Nat) (devices : List (Nat × Nat))
    (K seqB : B8) (hK : K.length = 60) (hs : seqB.length = 8)
    (a b : List Tls.W) (nPow : Nat) (hsh : Local.Ghash.Shared a b (HybridKernel.hashKeyOf K) nPow) :
    let statuses := (ds.map (DevSend.status c)).flatten
    let parts := splitEnvelopes (ds.map (DevSend.env c)) (ds.map (DevSend.sealed c)).flatten
    let envelopes := parts.map (·.2)
    let timestamp := (parts.headD ([], [])).1
    let newState := (ds.map fun d => d.kept c ++ (if d.kind = 0 then [] else d.pending)).flatten
    let records := ((deviceSpans 0 (ds.map (·.kind))).map fun s => (newState.drop s.1.1).take recordBytes).flatten
    let ctr := kernelOut (BundleKernel.bundleRequestCtr frame.length payloadAt (offsets.getD 0 0) (offsets.getD 1 0)
      devices) (requestIn K seqB records frame mask)
    let head := (ctr.drop 1).take (5 + innerOf frame.length)
    let pad := (ctr.drop (1 + 5 + innerOf frame.length)).take 16
    let hA := Local.Ghash.toBytes (Local.Ghash.half a (head.take 5) (head.drop 5))
    let hB := Local.Ghash.toBytes (Local.Ghash.half b (head.take 5) (head.drop 5))
    statuses = List.replicate ds.length 255 →
    PublicRequest.buildDevices envelopes (beNat timestamp) id mask c.official = .ok (frame, payloadAt, offsets) →
    BundleKernel.pairs (offsets.drop 2) = some devices →
    ctr.take 1 = [255] →
    Local.Ghash.needed 5 (innerOf frame.length) ≤ nPow →
    let msg := PublicRequest.devicesMessage (ds.map (DevSend.reference c)) (beNat c.timestamp) id c.official
    (∀ d ∈ ds, d.status c = [255] ∧ d.kept c = d.advanced c) ∧
    envelopes = ds.map (DevSend.reference c) ∧
    timestamp = c.timestamp ∧
    records = (ds.map (DevSend.advanced c)).flatten ∧
    head ++ kernelOut HybridKernel.gcmTag (pad ++ (hA ++ hB)) =
      TlsRecord.sealCore Gcm.concrete ((K.drop 32).take 16) ((K.drop 48).take 12) seqB
        (KernelSpecs.RequestFrame.assembleHeader (PublicRequest.total msg) mask ++
          KernelSpecs.RequestFrame.maskFrom mask 0
            (KernelSpecs.RequestFrame.render
              (KernelSpecs.RequestFrame.devicesValues (ds.map (DevSend.advanced c)).flatten) msg))
        23 0 := by
  intro statuses parts envelopes timestamp newState records ctr head pad hA hB hgate hbuilt hpairs hacc hn msg
  -- every status is 255
  have hl1 : ∀ s ∈ ds.map (DevSend.status c), s.length = 1 := by
    intro s hsm
    obtain ⟨d, hdm, rfl⟩ := List.mem_map.mp hsm
    exact DevSend.status_length c d hc (hd d hdm)
  have hall : ∀ d ∈ ds, d.status c = [255] := by
    have e := (gate_iff _ hl1).mp (by rw [List.length_map]; exact hgate)
    intro d hdm
    exact e _ (List.mem_map_of_mem hdm)
  have hdev : ∀ d ∈ ds, d.kept c = d.advanced c ∧ d.sealed c = c.timestamp ++ d.reference c :=
    fun d hdm => DevSend.accepted c d hc (hd d hdm) (hall d hdm)
  have hts8 := DevCtx.timestamp_length c hc
  have hrefl : ∀ d ∈ ds, (d.reference c).length = d.env c := by
    intro d hdm
    have h1 := DevSend.sealed_length c d hc (hd d hdm)
    rw [(hdev d hdm).2, List.length_append, hts8] at h1
    omega
  -- the envelopes, cut out of the one opening
  have hparts : parts = ds.map fun d => (c.timestamp, d.reference c) := by
    have e1 : ds.map (DevSend.sealed c) = (ds.map fun d => (c.timestamp, d.reference c)).map (fun p => p.1 ++ p.2) := by
      rw [List.map_map]
      exact List.map_congr_left (fun d hdm => (hdev d hdm).2)
    have e2 : ds.map (DevSend.env c) = (ds.map fun d => (c.timestamp, d.reference c)).map (·.2.length) := by
      rw [List.map_map]
      exact List.map_congr_left (fun d hdm => (hrefl d hdm).symm)
    show splitEnvelopes (ds.map (DevSend.env c)) (ds.map (DevSend.sealed c)).flatten = _
    rw [e1, e2]
    refine splitEnvelopes_flatten _ (fun p hp => ?_)
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp hp
    exact hts8
  have henv : envelopes = ds.map (DevSend.reference c) := by
    show parts.map (·.2) = _
    rw [hparts, List.map_map]
    rfl
  have hts : timestamp = c.timestamp := by
    show (parts.headD ([], [])).1 = _
    rw [hparts]
    cases ds with
    | nil => exact absurd rfl hne
    | cons d ds => rfl
  -- op 62's records
  have hrec : records = (ds.map (DevSend.advanced c)).flatten := by
    have := spans_records (DevSend.kept c) ds [] (fun d hdm => ⟨DevSend.kept_length c d hc (hd d hdm), fun h0 =>
      ((hd d hdm).bundleOk h0).1⟩)
    simp only [List.length_nil, List.nil_append] at this
    show ((deviceSpans 0 (ds.map (·.kind))).map fun s => (newState.drop s.1.1).take recordBytes).flatten = _
    rw [this]
    congr 1
    exact List.map_congr_left (fun d hdm => (hdev d hdm).1)
  refine ⟨fun d hdm => ⟨hall d hdm, (hdev d hdm).1⟩, henv, hts, hrec, ?_⟩
  -- the request
  rw [henv, hts] at hbuilt
  have hdl := devices_length _ _ _ _ _ _ _ _ hbuilt devices hpairs
  have hadv : ∀ d ∈ ds, (d.advanced c).length = recordBytes := by
    intro d hdm
    rw [← (hdev d hdm).1]
    exact DevSend.kept_length c d hc (hd d hdm)
  have hrl : ((ds.map (DevSend.advanced c)).flatten).length = recordBytes * devices.length := by
    rw [hdl, List.length_map, List.length_flatten, List.map_map]
    have : ds.map ((·.length) ∘ DevSend.advanced c) = ds.map (fun _ => recordBytes) :=
      List.map_congr_left (fun d hdm => hadv d hdm)
    rw [this, sum_map_const']
  have hval := bundleRequestCtr_value (ds.map (DevSend.reference c)) (beNat c.timestamp) id mask frame c.official
    payloadAt offsets hbuilt devices hpairs K seqB _ hK hs hrl
  have hPl := bundlePlain_length (ds.map (DevSend.reference c)) (beNat c.timestamp) id mask frame c.official
    payloadAt offsets hbuilt devices hpairs K seqB _ hK hs hrl
  simp only at hval hPl
  have hctr : ctr = (KernelSpecs.sealedRequest K seqB
      (KernelSpecs.RequestFrame.assembleHeader (PublicRequest.total msg) mask ++
        KernelSpecs.RequestFrame.maskFrom mask 0
          (KernelSpecs.RequestFrame.render
            (KernelSpecs.RequestFrame.devicesValues (ds.map (DevSend.advanced c)).flatten) msg))
      (KernelSpecs.bundleRequestValue (ds.map (DevSend.advanced c)).flatten (offsets.getD 0 0) (offsets.getD 1 0)
        devices).1).flatten := by
    show kernelOut _ (requestIn K seqB records frame mask) = _
    rw [hrec]
    show (List.map _ _).flatten = _
    rw [hval]
  exact sealed_record K seqB _ _ hK frame.length hPl a b nPow hsh hn ctr hctr hacc

/-! ## All or nothing -/

/-- **A refused gate releases nothing more and keeps the state.** After the one status opening, if
the opened statuses are not all 255, `afterStatuses` frees the new records, the timestamps ‖
envelopes and the copied pending blocks, opens nothing and returns `none`. -/
theorem devices_refused (n m : Nat) (a : DevicesArgs) (envs : List Nat) (st : Bits)
    (h : st ≠ bitsOf (List.replicate m 255)) :
    Silent (afterStatuses n m a envs st) ∧ afterStatuses n m a envs st =
      seqs ([.freeBool ⟨statusId n m⟩] ++ frees ((indexed a.devices).map fun (i, _) => ⟨sealBase n m i + 4⟩) ++
        frees ((indexed a.devices).map fun (i, _) => ⟨sealBase n m i + 5⟩) ++ frees (pendings n a.devices))
        (.done none) := by
  unfold afterStatuses
  dsimp only
  rw [if_neg h]
  refine ⟨Silent.seqs (Silent.done _) _ (fun x hx => plain_label x ?_), rfl⟩
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with ((rfl | hx) | hx) | hx <;> first | rfl | exact frees_plain' _ _ hx

/-- **All or nothing** (the C++ opened device k's envelope before device k + 1's status): when the
script's opened statuses are the devices' status slices and some device's status is not 255, the rest
of op 61 releases nothing, to anyone, against any adversary: no envelope of any device is opened. -/
theorem devices_refused_view (E : Env) (me : Party) (adv : Adversary) (c : DevCtx) (ds : List DevSend)
    (hc : c.Ok) (hd : ∀ d ∈ ds, d.Ok c) (hbad : ∃ d ∈ ds, d.status c ≠ [255])
    (n : Nat) (a : DevicesArgs) (envs : List Nat) (σ : Store) (I : Ideal) (vD : List Release) :
    let st := bitsOf (ds.map (DevSend.status c)).flatten
    st ≠ bitsOf (List.replicate ds.length 255) ∧
    Silent (afterStatuses n ds.length a envs st) ∧
    (withAdv E me adv (afterStatuses n ds.length a envs st) σ I vD).viewD = [] ∧
    (withAdv E me adv (afterStatuses n ds.length a envs st) σ I vD).viewH = [] := by
  intro st
  have hl1 : ∀ s ∈ ds.map (DevSend.status c), s.length = 1 := by
    intro s hsm
    obtain ⟨d, hdm, rfl⟩ := List.mem_map.mp hsm
    exact DevSend.status_length c d hc (hd d hdm)
  have hne : st ≠ bitsOf (List.replicate ds.length 255) := by
    intro e
    have e' : bitsOf (ds.map (DevSend.status c)).flatten = bitsOf (List.replicate (ds.map (DevSend.status c)).length 255) := by
      rw [List.length_map]; exact e
    have hall := (gate_bits _ hl1).mp e'
    obtain ⟨d, hdm, hbd⟩ := hbad
    exact hbd (hall _ (List.mem_map_of_mem hdm))
  obtain ⟨hsil, -⟩ := devices_refused n ds.length a envs st hne
  exact ⟨hne, hsil, (silent_view E me adv _ hsil σ I vD).1, (silent_view E me adv _ hsil σ I vD).2⟩

end TlsMpc.Node.Flows.Send
