import TlsMpc.Node.Flows.Receive
import TlsMpc.KernelSpecs.ReceiveAcceptAccessKey

/-!
# Receive a first message: T13 / T4-RECV at the function level, the refusals, WF

REORGANIZATION_PLAN.md stage S14 (8.1: T3, T4-RECV, T13). About the scripts of
`Flows/Receive.lean`. No I/O; no emitter imports this module.

THE PIPELINE. `Pipeline.In` collects what the two scripts compute in the engines, as bytes: the
envelope, our identity key, the agreements (S11), the field engine's words (the server point, `rx`,
`ry`, the base key's checks), our inputs, and the public shapes the stages opened. Each stage is the
kernel's SPECIFICATION as `ReceiveProofs.*_spec` states the kernel (`unsealStaticV`, …,
`accessKeyV`: the kernel's output fields, in its output order, on its input parts, in its input
order), and the stages are connected by THE SCRIPT'S OWN WIRING FUNCTIONS (`Receive.staticIn`,
`messageIn`, `contentIn`, `certificateIn`, `verifiedIn`, `prekeyOpenIn`, `heldOf`,
`sessionInOf`, `textIn`, `accessKeyIn`), the same definitions the scripts apply to handles. So the
hypothesis the kernel-level theorems take about the controller's wiring ("the session's `verified`
byte is `receive-certificate-verified`'s output on `receive-certificate`'s validity and
signature") holds BY DEFINITION here (`pipeline_verified_wiring`, `rfl`), and
`ReceiveAccept.session_accept_certificate` applies with no wiring hypothesis.

PROVED (standard axioms only):
  * `pipeline_verified_wiring`: the session's `verified` input is `receive-certificate-verified` on
    `receive-certificate`'s outputs 0 and 3 (by the script's wiring).
  * **T13** `pipeline_accept_certificate`: the session's status 255 implies the message MAC verified
    under libsignal's keys (counter `n ≤ jump`, post-quantum index `1 + i`), the sender
    certificate's checks passed (identity key = the decrypted static key, trusted signer, expiry),
    the server key decoded to a curve point, and the signature's `R` is the compression of the
    field engine's `[s]B − [h]A` (`session_accept_certificate`, `certificate_valid`,
    `certificateVerified_iff`, `session_status_iff`).
  * **T4-RECV** `pipeline_accept_outputs`: then the plaintext the text and access-key kernels read is
    the AES-256-CBC decryption with PKCS#7 unpadding under libsignal's keys (`CbcOpen.openCore`), and
    the conversation record is the send kernels' record from the session keys
    (`session_accept_outputs`); `pipeline_text`: with the text's status 255 too, the opened text is
    exactly the body of that decrypted content (`ReceiveAcceptText.text_status`, `text_accepted`);
    `pipeline_record`: with the access key's status 255, the stored record is the conversation
    with the access key derived from the message's profile key, for one of the 72 layouts
    (`withAccessKey_status`, `withAccessKey_accepted`).
  * The refusals (T3's "a refused message shows at most the status and the shapes"):
    `pipeline_refused_text_zero` (`text_zero_unless_accepted`: the text kernel's outputs are zero
    unless the session accepted; the script does not even run it, `Receive.sessionRest_refused`);
    `pipeline_certificateLength_zero`, `pipeline_contentShape_zero`, `pipeline_prekeyShape_zero`,
    `pipeline_prekeyIds_zero`, `pipeline_signalShape_zero`: each opened shape / id is all zero when
    the stage before it was not valid (`unsealMessage_rejects`, `contentShape_rejects`,
    `prekeyShape_rejects`, `prekeyOpen_rejects`, `signalShape_rejects`).
  * WF: `dropScript_frees_wf` (freeing live distinct handles: drop and every refusal's frees). The
    WF of `takeScript`, `openFirst`, `session` is open (S14_NOTES.md, gap F25): the vectors pass
    `checkBatch` on every batch.
  * `Wire.Bounded`: `stageInstrs_bounded` (every kernel stage).
  * The provisional ids: `Receive.provisionalId_inj`, `provisionalId_high`.

NOT PROVED (S14_NOTES.md, gaps): that the model run of the scripts computes the pipeline (it needs
S10's conversions' and S11's agreements' run-level specifications and the receive kernels as model
circuits with word inputs); the curve's own correctness (S11); the KEM decapsulation (a local tool).
-/

namespace TlsMpc.Node.Flows.Receive.Proofs

open TlsMpc TlsMpc.Signal TlsMpc.Signal.ReceiveFirst
open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Receive
open TlsMpc.KernelSpecs.ReceiveAccept

abbrev Bs := List (BitVec 8)

/-! ## Each kernel's outputs on bytes (`ReceiveProofs.*_spec`), parts in the kernel's input order -/

namespace Pipeline

/-- `receive-unseal-static` (`unsealStatic_spec`): staticValid, senderIdentity, senderPoint (the
same bytes), chain. Inputs: envelope, ourIdentity, agreement. -/
def unsealStaticV (size : Nat) (ps : List Bs) : List Bs :=
  let out := unsealStatic Aes.concrete Sha256.concrete ByteAuth.concrete size (ps.getD 1 []) (ps.getD 0 []) (ps.getD 2 [])
  [out.getD 0 [], out.getD 1 [], out.getD 1 [], out.getD 2 []]

/-- `receive-unseal-message` (`unsealMessage_spec`): valid, content, certificateLength. -/
def unsealMessageV (size : Nat) (ps : List Bs) : List Bs :=
  unsealMessage Aes.concrete Sha256.concrete ByteAuth.concrete size (ps.getD 0 []) (ps.getD 1 []) (ps.getD 2 [])
    (ps.getD 3 [])

/-- `receive-content-shape` (`contentShape_spec`). -/
def contentShapeV (u cert : Nat) (ps : List Bs) : List Bs :=
  contentShape ByteAuth.concrete u cert (ps.getD 0 []) (ps.getD 1 [])

/-- `receive-content` (`content_spec`): valid, messageType, certificate, message. -/
def contentV (u cert : Nat) (hint : Bool) (ps : List Bs) : List Bs :=
  ReceiveFirst.contentParts ByteAuth.concrete u cert hint (ps.getD 0 []) (ps.getD 1 [])

/-- `receive-certificate` (`certificate_spec`): certificateValid, uuid, deviceId, signature, flip,
challenge, scalar. -/
def certificateV (cert : Nat) (c : CertShape) (ps : List Bs) : List Bs :=
  let out := certificate ByteAuth.concrete XEdDsaSha512.concrete XEdDsaScalar.concrete cert c (ps.getD 0 [])
    (ps.getD 1 []) (ps.getD 2 []) (ps.getD 3 []) (ps.getD 4 []) (ps.getD 5 []) (ps.getD 6 [])
  [out.getD 0 [], out.getD 1 [], out.getD 2 [], out.getD 3 [], out.getD 4 [], out.getD 5 [], (out.getD 3 []).drop 32]

/-- `receive-certificate-verified` (`certificateVerified_spec`). -/
def verifiedV (ps : List Bs) : List Bs :=
  certificateVerified ByteAuth.concrete (ps.getD 0 []) (ps.getD 1 []) (ps.getD 2 []) (ps.getD 3 []) (ps.getD 4 [])

/-- `receive-prekey-shape` (`prekeyShape_spec`). -/
def prekeyShapeV (n : Nat) (ps : List Bs) : List Bs := prekeyShape ByteAuth.concrete n (ps.getD 0 []) (ps.getD 1 [])

/-- `receive-prekey-open` (`prekeyOpen_spec`). -/
def prekeyOpenV (p : PreKeyShape) (n : Nat) (ps : List Bs) : List Bs :=
  prekeyOpen ByteAuth.concrete p n (ps.getD 0 []) (ps.getD 1 []) (ps.getD 2 []) (ps.getD 3 [])

/-- `receive-signal-shape` (`signalShape_spec`). -/
def signalShapeV (p : PreKeyShape) (n : Nat) (ps : List Bs) : List Bs :=
  signalShape ByteAuth.concrete p n (ps.getD 0 []) (ps.getD 1 [])

/-- `receive-session` (`session_spec`; `dh4` absent reads as no bytes). -/
def sessionV (p : PreKeyShape) (q : SignalShape) (n jump : Nat) (x : SessionIn Bs) : List Bs :=
  let out := ReceiveFirst.session AesInverse.concrete Sha256.concrete ByteAuth.concrete p q n jump x.message
    (x.prekeyValid ++ x.verified) x.senderIdentity x.ourIdentity x.localAddress x.uuid x.deviceId x.dh1 x.dh2 x.dh3
    (x.dh4.getD []) x.kemSecret x.receiveAgreement x.sendAgreement x.ratchetPublic x.baseValid x.torsionX x.torsionY
    x.certificate x.accessKey x.requestId
  [out.getD 0 [], out.getD 1 [], out.getD 2 [], out.getD 3 []]

/-- `receive-text` (`text_spec`). -/
def textV (cap : Nat) (ps : List Bs) : List Bs :=
  let out := text ByteAuth.concrete cap (ps.getD 0 [])
  [out.getD 0 [], out.getD 1 [], out.getD 2 [], out.getD 3 []]

/-- `receive-access-key` (`accessKey_spec`). -/
def accessKeyV (cert offset : Nat) (ps : List Bs) : List Bs :=
  let out := withAccessKey Aes.concrete ByteAuth.concrete cert offset (ps.getD 0 []) (ps.getD 1 [])
  [out.getD 0 [], out.getD 1 []]

/-- What the scripts compute in the engines, as bytes, and the public shapes they opened. -/
structure In where
  envelope : Bs
  size : Nat
  /-- Our identity public key. -/
  ours : Bs
  /-- S11's two agreements with our identity key (ephemeral, then the sender's static key). -/
  agreement1 : Bs
  agreement2 : Bs
  /-- The content's size and the certificate's length, hint and layout (opened shapes). -/
  u : Nat
  cert : Nat
  hint : Bool
  c : CertShape
  /-- The public inputs of the certificate check: the trusted signer, the time, the server point. -/
  signer : Bs
  now : Bs
  serverX : Bs
  serverY : Bs
  /-- The field engine's words: the server key is a point (1), the signature's `[s]B − [h]A`. -/
  serverValid : Bs
  rx : Bs
  ry : Bs
  /-- The PreKey message's size and layout, and whether it names a one-time prekey. -/
  n : Nat
  p : PreKeyShape
  oneTime : Bool
  /-- S11's agreements of the session, in `sessionJobs`' order. -/
  ag : List Bs
  /-- The base key's checks (field engine), our inputs. -/
  baseValid : Bs
  torsionX : Bs
  torsionY : Bs
  kem : Bs
  address : Bs
  accessKey : Bs
  requestId : Bs
  certificate : Bs
  /-- The Signal message's layout, `SIGNAL_RECEIVE_JUMP`, the text's capacity, the access key's
  offset (opened shapes). -/
  q : SignalShape
  jump : Nat
  cap : Nat
  offset : Nat
  ownCert : Nat

variable (i : In)

def us : List Bs := unsealStaticV i.size (staticIn i.envelope i.ours i.agreement1)
def um : List Bs := unsealMessageV i.size (messageIn i.envelope (us i) i.agreement2)
def ct : List Bs := contentV i.u i.cert i.hint (contentIn (um i))
def ce : List Bs := certificateV i.cert i.c (certificateIn (ct i) (us i) i.signer i.now i.serverX i.serverY)
def ve : List Bs := verifiedV (verifiedIn (ce i) i.serverValid i.rx i.ry)
def po : List Bs := prekeyOpenV i.p i.n (prekeyOpenIn (ct i) (us i))
def held : Held Bs := heldOf (us i) (ct i) (ce i) (ve i) (po i) i.ours
def sin : SessionIn Bs :=
  sessionInOf (held i) i.ag i.oneTime i.baseValid i.torsionX i.torsionY i.kem i.address i.accessKey i.requestId
    i.certificate
def se : List Bs := sessionV i.p i.q i.n i.jump (sin i)
def tx : List Bs := textV i.cap (textIn (se i))
def ak : List Bs := accessKeyV i.ownCert i.offset (accessKeyIn (se i))

/-- The certificate kernel's arguments in the pipeline, by name. -/
def certBytes : Bs := (ct i).getD 2 []
def contentValid : Bs := (ct i).getD 0 []
def senderIdentity : Bs := (us i).getD 1 []

end Pipeline

open Pipeline

/-! ## The wiring, by definition -/

/-- **The session's `verified` input is `receive-certificate-verified` on `receive-certificate`'s
validity and signature** (outputs 0 and 3), with the server key's validity word and the field
engine's `rx`, `ry`: the script's wiring (`verifiedIn`, `heldOf`, `sessionInOf`). This is the
hypothesis `ReceiveAccept.session_accept_certificate` takes about the controller; here it holds by
the scripts' definitions. -/
theorem pipeline_verified_wiring (i : In) :
    (sin i).verified =
      (certificateVerified ByteAuth.concrete
        ((certificate ByteAuth.concrete XEdDsaSha512.concrete XEdDsaScalar.concrete i.cert i.c (certBytes i)
          (contentValid i) (senderIdentity i) i.signer i.now i.serverX i.serverY).getD 0 [])
        ((certificate ByteAuth.concrete XEdDsaSha512.concrete XEdDsaScalar.concrete i.cert i.c (certBytes i)
          (contentValid i) (senderIdentity i) i.signer i.now i.serverX i.serverY).getD 3 [])
        i.serverValid i.rx i.ry).getD 0 [] := rfl

/-- The session's status as `ReceiveAccept.session_accept_certificate` reads it. -/
theorem pipeline_status (i : In) :
    (se i).getD 0 [] =
      (ReceiveFirst.session AesInverse.concrete Sha256.concrete ByteAuth.concrete i.p i.q i.n i.jump (sin i).message
        ((sin i).prekeyValid ++
          (certificateVerified ByteAuth.concrete
            ((certificate ByteAuth.concrete XEdDsaSha512.concrete XEdDsaScalar.concrete i.cert i.c (certBytes i)
              (contentValid i) (senderIdentity i) i.signer i.now i.serverX i.serverY).getD 0 [])
            ((certificate ByteAuth.concrete XEdDsaSha512.concrete XEdDsaScalar.concrete i.cert i.c (certBytes i)
              (contentValid i) (senderIdentity i) i.signer i.now i.serverX i.serverY).getD 3 [])
            i.serverValid i.rx i.ry).getD 0 [])
        (senderIdentity i) (sin i).ourIdentity (sin i).localAddress (sin i).uuid (sin i).deviceId (sin i).dh1
        (sin i).dh2 (sin i).dh3 ((sin i).dh4.getD []) (sin i).kemSecret (sin i).receiveAgreement (sin i).sendAgreement
        (sin i).ratchetPublic (sin i).baseValid (sin i).torsionX (sin i).torsionY (sin i).certificate
        (sin i).accessKey (sin i).requestId).getD 0 [] := by
  have hs : (sin i).senderIdentity = senderIdentity i := rfl
  show (sessionV i.p i.q i.n i.jump (sin i)).getD 0 [] = _
  simp only [sessionV, List.getD_cons_zero]
  rw [pipeline_verified_wiring, hs]

/-- The session's plaintext and conversation, by name. -/
theorem pipeline_se3 (i : In) :
    (se i).getD 3 [] = (ReceiveFirst.session AesInverse.concrete Sha256.concrete ByteAuth.concrete i.p i.q i.n i.jump
      (sin i).message ((sin i).prekeyValid ++ (sin i).verified) (sin i).senderIdentity (sin i).ourIdentity
      (sin i).localAddress (sin i).uuid (sin i).deviceId (sin i).dh1 (sin i).dh2 (sin i).dh3 ((sin i).dh4.getD [])
      (sin i).kemSecret (sin i).receiveAgreement (sin i).sendAgreement (sin i).ratchetPublic (sin i).baseValid
      (sin i).torsionX (sin i).torsionY (sin i).certificate (sin i).accessKey (sin i).requestId).getD 3 [] := by
  show (sessionV i.p i.q i.n i.jump (sin i)).getD 3 [] = _
  simp only [sessionV, List.getD_cons_succ, List.getD_cons_zero]

theorem pipeline_se1 (i : In) :
    (se i).getD 1 [] = (ReceiveFirst.session AesInverse.concrete Sha256.concrete ByteAuth.concrete i.p i.q i.n i.jump
      (sin i).message ((sin i).prekeyValid ++ (sin i).verified) (sin i).senderIdentity (sin i).ourIdentity
      (sin i).localAddress (sin i).uuid (sin i).deviceId (sin i).dh1 (sin i).dh2 (sin i).dh3 ((sin i).dh4.getD [])
      (sin i).kemSecret (sin i).receiveAgreement (sin i).sendAgreement (sin i).ratchetPublic (sin i).baseValid
      (sin i).torsionX (sin i).torsionY (sin i).certificate (sin i).accessKey (sin i).requestId).getD 1 [] := by
  show (sessionV i.p i.q i.n i.jump (sin i)).getD 1 [] = _
  simp only [sessionV, List.getD_cons_succ, List.getD_cons_zero]

theorem pipeline_se0 (i : In) :
    (se i).getD 0 [] = (ReceiveFirst.session AesInverse.concrete Sha256.concrete ByteAuth.concrete i.p i.q i.n i.jump
      (sin i).message ((sin i).prekeyValid ++ (sin i).verified) (sin i).senderIdentity (sin i).ourIdentity
      (sin i).localAddress (sin i).uuid (sin i).deviceId (sin i).dh1 (sin i).dh2 (sin i).dh3 ((sin i).dh4.getD [])
      (sin i).kemSecret (sin i).receiveAgreement (sin i).sendAgreement (sin i).ratchetPublic (sin i).baseValid
      (sin i).torsionX (sin i).torsionY (sin i).certificate (sin i).accessKey (sin i).requestId).getD 0 [] := by
  show (sessionV i.p i.q i.n i.jump (sin i)).getD 0 [] = _
  simp only [sessionV, List.getD_cons_zero]

theorem default_bs : (default : Bs) = [] := rfl

/-- The text kernel's outputs on the session's plaintext (`textIn`). -/
theorem pipeline_tx0 (i : In) :
    (tx i).getD 0 [] = (text ByteAuth.concrete i.cap ((se i).getD 3 [])).getD 0 [] := by
  show (textV i.cap (textIn (se i))).getD 0 [] = _
  simp only [textV, textIn, default_bs, List.getD_cons_zero]

theorem pipeline_tx2 (i : In) :
    (tx i).getD 2 [] = (text ByteAuth.concrete i.cap ((se i).getD 3 [])).getD 2 [] := by
  show (textV i.cap (textIn (se i))).getD 2 [] = _
  simp only [textV, textIn, default_bs, List.getD_cons_zero, List.getD_cons_succ]

/-- The access-key kernel's outputs on the session's conversation and plaintext (`accessKeyIn`). -/
theorem pipeline_ak0 (i : In) :
    (ak i).getD 0 [] = (withAccessKey Aes.concrete ByteAuth.concrete i.ownCert i.offset ((se i).getD 1 [])
      ((se i).getD 3 [])).getD 0 [] := by
  show (accessKeyV i.ownCert i.offset (accessKeyIn (se i))).getD 0 [] = _
  simp only [accessKeyV, accessKeyIn, default_bs, List.getD_cons_zero, List.getD_cons_succ]

theorem pipeline_ak1 (i : In) :
    (ak i).getD 1 [] = (withAccessKey Aes.concrete ByteAuth.concrete i.ownCert i.offset ((se i).getD 1 [])
      ((se i).getD 3 [])).getD 1 [] := by
  show (accessKeyV i.ownCert i.offset (accessKeyIn (se i))).getD 1 [] = _
  simp only [accessKeyV, accessKeyIn, default_bs, List.getD_cons_zero, List.getD_cons_succ]

/-! ## T13: what an accepted first message says about its sender certificate -/

/-- **T13, accept direction, for the scripts' wiring.** If `receive-session`'s status is 255 (the
only way the script reaches `receive-text`), then:
* the message MAC verified under libsignal's keys for some counter `n ≤ jump` and post-quantum
  index `1 + i` (`session_status_iff`);
* `receive-certificate` was valid (`certificate_valid`): the certificate's identity key is the
  sender's identity key decrypted from the envelope, its signer is the trusted one, and
  `now ≤ expires`;
* the server key decoded to a curve point (`serverValid` is 1), the signature's scalar is below
  2^253, and its `R` is the compression of the field engine's `[s]B − [h]A` (`rx`, `ry`), `h` being
  the certificate's XEdDSA challenge (`certificateVerified_iff`): the certificate chain to the
  trusted server key holds, given the field engine computed `[s]B − [h]A` (S11 / P-FIELDPROG). -/
theorem pipeline_accept_certificate (i : In) (hjump : i.jump ≤ 16) (h : (se i).getD 0 [] = [255]) :
    (∃ n, (n ≤ i.jump ∧ counterBytes i.q (signalWire i.p i.n (sin i).message) = numberBytes ByteAuth.concrete n) ∧
      ∃ k, (k ≤ i.jump ∧ pqIndexBytes i.q (i.p.signalSize i.n) (signalWire i.p i.n (sin i).message) =
          numberBytes ByteAuth.concrete (1 + k)) ∧
        MessageMac.tag Sha256.concrete
            (messageStep (keys Sha256.concrete (sin i).dh1 (sin i).dh2 (sin i).dh3 ((sin i).dh4.getD []) (sin i).kemSecret
              (sin i).receiveAgreement (sin i).sendAgreement) i.jump n k).material.macKey
            (senderIdentity i) (sin i).ourIdentity (MessageMac.content (signalWire i.p i.n (sin i).message)) =
          MessageMac.receivedTag (signalWire i.p i.n (sin i).message)) ∧
    (certificate ByteAuth.concrete XEdDsaSha512.concrete XEdDsaScalar.concrete i.cert i.c (certBytes i)
      (contentValid i) (senderIdentity i) i.signer i.now i.serverX i.serverY).getD 0 [] = [255] ∧
    Establish.part (certBytes i) (bodyAt i.cert + i.c.e164 + 14) 32 = senderIdentity i ∧
    Establish.part (certBytes i)
      (if i.c.embedded then bodyAt i.cert + i.c.e164 + 48 else bodyAt i.cert + i.c.e164 + 46 + 2 + i.c.uuidSize + 1)
      i.c.signerSize = i.signer ∧
    atMost ByteAuth.concrete i.now (Establish.part (certBytes i) (bodyAt i.cert + i.c.e164 + 3) 8).reverse = 255 ∧
    i.serverValid = ByteAuth.concrete.const 1 :: List.replicate 31 (ByteAuth.concrete.const 0) ∧
    (OpenResult.get ByteAuth.concrete (Establish.part (certBytes i) (bodyAt i.cert + i.c.body + 2) 64) 63 &&& 127).toNat
      < 32 ∧
    (Establish.part (certBytes i) (bodyAt i.cert + i.c.body + 2) 64).take 32 = XEdDsa.compress ByteAuth.concrete i.rx i.ry := by
  rw [pipeline_status] at h
  exact session_accept_certificate XEdDsaSha512.concrete XEdDsaScalar.concrete i.p i.q i.n i.jump hjump (h := h)

/-! ## T4-RECV: the decrypted text and the stored record -/

/-- **T4-RECV, the session.** If the status is 255 then, for the counter `n` and post-quantum index
`1 + k` of T13, the plaintext the text and access-key kernels read (`se[3]`) is the AES-256-CBC
decryption with PKCS#7 unpadding (`CbcOpen.openCore`, without its status byte) of the message's
ciphertext under libsignal's cipher key and IV for that counter (the reference decryption), and the
conversation record (`se[1]`) is our certificate followed by the send kernels' session built from
the session keys and the contact's metadata (`session_accept_outputs`). -/
theorem pipeline_accept_outputs (i : In) (hjump : i.jump ≤ 16) (h : (se i).getD 0 [] = [255]) :
    ∃ n k, (n ≤ i.jump ∧ counterBytes i.q (signalWire i.p i.n (sin i).message) = numberBytes ByteAuth.concrete n) ∧
      (k ≤ i.jump ∧ pqIndexBytes i.q (i.p.signalSize i.n) (signalWire i.p i.n (sin i).message) =
        numberBytes ByteAuth.concrete (1 + k)) ∧
      (se i).getD 1 [] =
        (sin i).certificate ++ Establish.session ByteAuth.concrete 80 (sin i).ratchetPublic
          (Establish.part (keys Sha256.concrete (sin i).dh1 (sin i).dh2 (sin i).dh3 ((sin i).dh4.getD []) (sin i).kemSecret
            (sin i).receiveAgreement (sin i).sendAgreement) 96 32)
          (Establish.part (keys Sha256.concrete (sin i).dh1 (sin i).dh2 (sin i).dh3 ((sin i).dh4.getD []) (sin i).kemSecret
            (sin i).receiveAgreement (sin i).sendAgreement) 192 32)
          (sin i).ourIdentity (senderIdentity i) ++
        Establish.metadata ByteAuth.concrete (sin i).uuid (sin i).accessKey (sin i).requestId (sin i).deviceId
          (varintValue ByteAuth.concrete (Establish.part (sin i).message (i.p.idsAt i.n + 1) i.p.registration)) ∧
      (se i).getD 3 [] =
        (CbcOpen.openCore AesInverse.concrete ByteAuth.concrete
          (messageStep (keys Sha256.concrete (sin i).dh1 (sin i).dh2 (sin i).dh3 ((sin i).dh4.getD []) (sin i).kemSecret
            (sin i).receiveAgreement (sin i).sendAgreement) i.jump n k).material.cipherKey
          (messageStep (keys Sha256.concrete (sin i).dh1 (sin i).dh2 (sin i).dh3 ((sin i).dh4.getD []) (sin i).kemSecret
            (sin i).receiveAgreement (sin i).sendAgreement) i.jump n k).material.iv
          (Establish.part (signalWire i.p i.n (sin i).message) i.q.cipherAt i.q.ciphertext)).drop 1 := by
  rw [pipeline_se0] at h
  obtain ⟨n, k, hn, hk, h1, _, h3⟩ := session_accept_outputs (hjump := hjump) (h := h)
  refine ⟨n, k, hn, hk, ?_, ?_⟩
  · rw [pipeline_se1, h1]; rfl
  · rw [pipeline_se3, h3]

/-- **The text kernel reads the session's plaintext** (the script's wiring, `textIn`). -/
theorem pipeline_text_input (i : In) : (tx i) = textV i.cap [(se i).getD 3 []] := rfl

/-- **T4-RECV, the text.** When the session's status is 255 and `receive-text`'s status is 255 (the
script opens the text only then), the opened text is exactly the body of the decrypted content
`c` (the session's plaintext after its 8-byte length, which `pipeline_accept_outputs` says is the
reference decryption): its `bodyLength c` bytes from `bodyStart c`, then zeros to the capacity
(`ReceiveAcceptText.text_status`, `text_accepted`; capacity below 65536, as `find` allows). -/
theorem pipeline_text (i : In) (hcap : i.cap < 65536) (ht : (tx i).getD 0 [] = [255]) :
    TlsMpc.KernelSpecs.ReceiveAcceptText.Accepted (((se i).getD 3 []).drop 8) i.cap ∧
    (tx i).getD 2 [] = (List.range i.cap).map (fun j =>
      if j < TlsMpc.KernelSpecs.ReceiveAcceptText.bodyLength (((se i).getD 3 []).drop 8) then
        TlsMpc.KernelSpecs.ReceiveAcceptText.g (((se i).getD 3 []).drop 8)
          (TlsMpc.KernelSpecs.ReceiveAcceptText.bodyStart (((se i).getD 3 []).drop 8) + j)
      else 0) := by
  have hs := TlsMpc.KernelSpecs.ReceiveAcceptText.text_status i.cap hcap ((se i).getD 3 [])
  rw [pipeline_tx0, hs, List.cons.injEq] at ht
  have hacc := (mk_eq_255 _).mp ht.1
  refine ⟨hacc, ?_⟩
  rw [pipeline_tx2, TlsMpc.KernelSpecs.ReceiveAcceptText.text_accepted i.cap hcap _ hacc]
  rfl

/-- **T4-RECV, the stored record.** When `receive-access-key`'s status is 255 (the script keeps the
record only then), some one of the 72 profile-key layouts matched and the access kernel's
conversation is the session's conversation with the access key (bytes `cert + 278 ..
cert + 294`) replaced by the one derived from the message's profile key; the stored contact record
is its bytes `cert .. cert + 319` (`withAccessKey_status`, `withAccessKey_accepted`). -/
theorem pipeline_record (i : In) (hlen : i.ownCert + 294 ≤ ((se i).getD 1 []).length)
    (hk : (ak i).getD 0 [] = [255]) :
    ∃ g ∈ TlsMpc.Signal.ReceiveFirst.gaps,
      (ak i).getD 1 [] = ((se i).getD 1 []).take (i.ownCert + 278) ++
        TlsMpc.KernelSpecs.ReceiveAcceptAccessKey.accessKeyOf
          (TlsMpc.KernelSpecs.ReceiveAcceptAccessKey.profileKey (((se i).getD 3 []).drop 8) i.offset g) ++
        ((se i).getD 1 []).drop (i.ownCert + 294) := by
  have hs := TlsMpc.KernelSpecs.ReceiveAcceptAccessKey.withAccessKey_status i.ownCert i.offset ((se i).getD 1 [])
    ((se i).getD 3 [])
  rw [pipeline_ak0, hs, List.cons.injEq] at hk
  obtain ⟨g, hg, hm⟩ := (mk_eq_255 _).mp hk.1
  refine ⟨g, hg, ?_⟩
  rw [pipeline_ak1, TlsMpc.KernelSpecs.ReceiveAcceptAccessKey.withAccessKey_accepted _ _ _ _ hlen g hg hm]
  rfl

/-! ## The refusals: what a refused message opens -/

/-- **A refused session opens no text**: if the session's status is not 255, every output of
`receive-text` on its plaintext is zero (`text_zero_unless_accepted`, kernel level:
`receiveText_gated`); the script does not run `receive-text` at all then
(`Receive.sessionRest_refused`). -/
theorem pipeline_refused_text_zero (i : In) (h : (se i).getD 0 [] ≠ [255]) :
    ∀ field ∈ text ByteAuth.concrete i.cap ((se i).getD 3 []), ∀ b ∈ field, b = 0 := by
  rw [pipeline_se0] at h
  rw [pipeline_se3]
  exact text_zero_unless_accepted (capacity := i.cap) (hne := h)

/-- **The opened certificate length is zero unless the sealed-sender layer verified**
(`unsealMessage_rejects`): for an envelope whose second half is refused, the adversary sees `00 00`
and the script refuses (no kernel takes that length). -/
theorem pipeline_certificateLength_zero (i : In) (h : (um i).getD 0 [] = [0]) :
    ∀ b ∈ (um i).getD 2 [], b = 0 :=
  fun b hb => ReceiveKernel.unsealMessage_rejects _ _ _ _ _ h _ (getD_mem _ 2 (by simp [unsealMessage])) b hb

/-- **The opened content shape is zero unless the content stage was valid** (`contentShape_rejects`). -/
theorem pipeline_contentShape_zero (i : In) (h : OpenResult.get ByteAuth.concrete ((um i).getD 0 []) 0 ≠ 255) :
    ∀ field ∈ contentShapeV i.u i.cert (contentIn (um i)), ∀ b ∈ field, b = 0 :=
  contentShape_rejects _ _ _ _ h

/-- **The opened prekey shape is zero unless the content was valid** (`prekeyShape_rejects`). -/
theorem pipeline_prekeyShape_zero (i : In) (h : OpenResult.get ByteAuth.concrete ((ct i).getD 0 []) 0 ≠ 255) :
    ∀ field ∈ prekeyShapeV i.n (prekeyShapeIn (ct i)), ∀ b ∈ field, b = 0 :=
  prekeyShape_rejects _ _ _ h

/-- **The opened prekey ids and Kyber ciphertext are zero unless the PreKey stage was valid**
(`prekeyOpen_rejects`). -/
theorem pipeline_prekeyIds_zero (i : In) (h : (po i).getD 0 [] = [0]) :
    ∀ field ∈ po i, ∀ b ∈ field, b = 0 :=
  ReceiveKernel.prekeyOpen_rejects _ _ _ _ _ _ h

/-- **The opened Signal shape is zero unless the PreKey stage was valid** (`signalShape_rejects`). -/
theorem pipeline_signalShape_zero (i : In) (h : OpenResult.get ByteAuth.concrete ((held i).prekeyValid) 0 ≠ 255) :
    ∀ field ∈ signalShapeV i.p i.n (signalShapeIn (held i)), ∀ b ∈ field, b = 0 :=
  signalShape_rejects _ _ _ _ h

/-! ## The layouts and names the scripts use -/

/-- The certificate kernel's output widths are `certificateOut` (its first, third fields one byte,
the UUID 16, the signature 64 bytes, the challenge's bits 1, 256, 253). -/
theorem certificateOut_sum : certificateOut.sum = 1166 := rfl

theorem prekeyOpenOut_sum : prekeyOpenOut.sum = 13158 := rfl

theorem kname_nil (s : String) : kname s [] = ascii s := rfl

/-- `receive-certificate-verified`'s name has no parameter. -/
theorem verifiedName_eq : verifiedName = ascii "receive-certificate-verified" := rfl

/-! ## Well-formedness of the small scripts -/

open TlsMpc.Node.Flows.Contacts (Fresh push check_freeBool' frees_wfp WFP_seq)

/-- **Drop is well formed** from any context in which the held handles are live and distinct:
it frees them. -/
theorem dropScript_frees_wf (sigs : Bytes → Option Sig) (c : Ctx) (hs : List BoolH) (hn : (hs.map (·.id)).Nodup)
    (hl : ∀ h ∈ hs, (c.bool? h).isSome = true) :
    WF sigs c (Contacts.seqs (Contacts.frees hs) (.done ())) :=
  (frees_wfp sigs (Q := fun _ (_ : Unit) => True) (.done ()) hs c hn hl (fun c' _ _ => WFP.done c' () trivial)).wf

/-! ## The pipe bound of the stages -/

theorem cuts_lt (B : Nat) : ∀ (lo : Nat) (ws : List Nat), lo + ws.sum < B → ∀ e ∈ cuts lo ws, e.1 < B ∧ e.2 < B
  | _, [], _ => by simp [cuts]
  | lo, w :: ws, h => by
    intro e he
    simp only [cuts, List.mem_cons] at he
    simp only [List.sum_cons] at h
    rcases he with rfl | he
    · exact ⟨by omega, by omega⟩
    · exact cuts_lt B (lo + w) ws (by omega) e he

theorem cuts_length : ∀ (lo : Nat) (ws : List Nat), (cuts lo ws).length = ws.length
  | _, [] => rfl
  | lo, w :: ws => by simp [cuts, cuts_length (lo + w) ws]

/-- **A stage's instructions fit the pipe** when its ids, its parts' ids, its name's length and its
layout's total are below 2^64. -/
theorem stageInstrs_bounded (n : Nat) (name : Bytes) (parts : List BoolH) (widths : List Nat)
    (hn : n + 2 + widths.length < B64) (hp : parts.length < B64) (hpi : ∀ g ∈ parts, g.id < B64)
    (hname : name.length < B64) (hw : widths.sum < B64) :
    ∀ ins ∈ stageInstrs n name parts widths, Instr.Bounded ins := by
  intro ins hi
  simp only [stageInstrs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hi
  rcases hi with (h | h) | h | h
  · rcases h with rfl | rfl
    · simp only [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank]
      exact ⟨by omega, hp, hpi⟩
    · simp only [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank]
      exact ⟨by omega, hname, by decide, by omega⟩
  · obtain ⟨e, he, rfl⟩ := h
    have hlen := List.mem_zipIdx he
    have hmem : e.1 ∈ cuts 0 widths := by
      rw [hlen.2.2]
      exact List.getElem_mem _
    have hc := cuts_lt B64 0 widths (by omega) e.1 hmem
    simp only [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank]
    have h2 := hlen.2.1
    rw [cuts_length] at h2
    exact ⟨by omega, by omega, hc.1, hc.2⟩
  · subst h; simp only [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank]; omega
  · subst h; simp only [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank]; omega

#print axioms pipeline_accept_certificate
#print axioms pipeline_accept_outputs
#print axioms pipeline_text
#print axioms pipeline_record
#print axioms pipeline_refused_text_zero
#print axioms pipeline_certificateLength_zero
#print axioms stageInstrs_bounded

end TlsMpc.Node.Flows.Receive.Proofs
