import TlsMpc.KernelSpecs.SealSend
import TlsMpc.KernelSpecs.RequestFrame

/-!
# What the Signal server receives for a send (T7: (b) composed with (a))

New file; it changes no definition and no emitter imports it. It depends on
`TlsMpc/KernelSpecs/RequestFrame.lean` only through `RequestFrame.signalRequestCtr_built` and the
names in its statement (`buildHeader`, `maskFrom`, `render`, `requestValues`), so a change of the
request builders touches this file only.

`serverReceives_accepted`: when `signal-seal-official` / `signal-seal-built` opened status 255 and
the controller built the request frame with the opened envelope (`PublicRequest.build`), the
`signal-request-ctr` kernel's outputs are the TLS record (`sealedRequest`) of the masked WebSocket
frame of `sendMessage envelope timestamp id official` with the contact's UUID, access key, device
and registration ids in their slots, where `envelope` is `Reference.sealV1` (sealed sender v1) of
the Signal message produced by the reference send step `SpqrSend.canonical` from the stored state.

Trusted, not proved (as in RequestFrame.lean): the C++ worker passes the opened envelope and the
controller's frame, mask and offsets unchanged (the hypotheses `built`, `hframe`, `hmask`); the
timestamp and request id are the controller's (free here).
-/
namespace TlsMpc.KernelSpecs.SealFrame
open Std.Tactic.BVDecide
open TlsMpc TlsMpc.Signal
open TlsMpc.KernelSpecs.SealFixed (stagedOf inputOf contentBytes sealInputs)
open TlsMpc.KernelSpecs.SealValue (Byte)
open TlsMpc.KernelSpecs.SealValue.Reference (sealV1)
open TlsMpc.KernelSpecs.SealSend (sealValue signalSeal_value sealValue_accepted)
open PublicRequest (sendMessage build total)
open TlsMpc.KernelSpecs.RequestFrame (buildHeader maskFrom render requestValues signalRequestCtr_built)
open TlsMpc.HybridKernel (lookup)

/-- **The bytes the server receives for an accepted send.** -/
theorem serverReceives_accepted (cert counterWidth previousWidth epochWidth indexWidth classes : Nat)
    (official : Bool) (sealAssign : BVExpr.Assignment)
    (hbound : cert + contentBytes classes official + counterWidth + previousWidth + epochWidth + indexWidth < 2 ^ 31)
    (accepted : ((HybridKernel.signalSealFixed cert counterWidth previousWidth epochWidth indexWidth true classes
      official).outputs.map (fun field => field.value.map (BVExpr.eval sealAssign))).getD 0 [] = [255])
    (timestamp id : Nat) (mask frame : List Byte) (offsets : List Nat)
    (built : build (((HybridKernel.signalSealFixed cert counterWidth previousWidth epochWidth indexWidth true classes
      official).outputs.map (fun field => field.value.map (BVExpr.eval sealAssign))).getD 3 [])
      timestamp id mask official = .ok (frame, offsets))
    (assign : BVExpr.Assignment)
    (hframe : (lookup (signalRequestInputs cert frame.length) "frame").map (BVExpr.eval assign) = frame)
    (hmask : (lookup (signalRequestInputs cert frame.length) "mask").map (BVExpr.eval assign) = mask) :
    let get := fun name => (lookup (sealInputs cert classes official) name).map (BVExpr.eval sealAssign)
    let record := get "conversation"
    let text := get "text"
    let shape : Serialization.Shape := ⟨counterWidth, previousWidth, false⟩
    let pqShape : SpqrMessage.Shape := ⟨epochWidth, indexWidth, 1, false⟩
    let i := inputOf 0 (stagedOf ((record.drop cert).take (182 + 80)) text) text (contentBytes classes official)
    let envelope := sealV1 i.receiver (get "ephemeralPublic") (get "senderPublic") (get "ephemeralAgreement")
      (get "staticAgreement") ((record.drop 0).take cert) (SpqrSend.canonical shape pqShape i).wire
    let msg := sendMessage envelope timestamp id official
    let requestGet := fun name => (lookup (signalRequestInputs cert frame.length) name).map (BVExpr.eval assign)
    SpqrSend.accepted shape pqShape i ∧
    (HybridKernel.signalRequestCtr cert frame.length (offsets.getD 0 0) (offsets.getD 1 0) (offsets.getD 2 0)
        (offsets.getD 3 0)).outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      sealedRequest (requestGet "clientApplication") (requestGet "sequence")
        (buildHeader (total msg) mask ++ maskFrom mask 0 (render (requestValues cert (requestGet "conversation")) msg))
        (signalRequestSlots cert 0 0 0 0 (requestGet "conversation")).1 := by
  intro get record text shape pqShape i envelope msg requestGet
  have hv := signalSeal_value cert counterWidth previousWidth epochWidth indexWidth classes official sealAssign hbound
  rw [hv] at accepted built
  have facts := sealValue_accepted _ _ _ _ _ _ _ _ _ _ _ _ accepted
  have henv : (sealValue cert counterWidth previousWidth epochWidth indexWidth (contentBytes classes official)
      (get "conversation") (get "text") (get "ephemeralPublic") (get "senderPublic") (get "ephemeralAgreement")
      (get "staticAgreement")).getD 3 [] = envelope := facts.2.2.2.2
  rw [henv] at built
  exact ⟨facts.1, signalRequestCtr_built envelope timestamp id mask frame official offsets built cert assign hframe hmask⟩

#print axioms serverReceives_accepted

end TlsMpc.KernelSpecs.SealFrame
