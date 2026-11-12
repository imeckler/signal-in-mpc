import TlsMpc.KernelSpecs.EstablishDevices
import TlsMpc.KernelSpecs.RequestFrame

/-!
# What the Signal server receives for a send to several new devices (multi-device track, part 2)

New file; it changes no definition and no emitter imports it. It is the ONLY file of this track
that depends on `TlsMpc/KernelSpecs/RequestFrame.lean`, and only through the headline theorem
`RequestFrame.bundleRequestCtr_built`, the builders `PublicRequest.buildDevices` /
`devicesMessage` / `total` and the names in that theorem's statement (`assembleHeader`, `maskFrom`,
`render`, `devicesValues`, `requestInputsOf`, `bundleRequestValue`, `sealedRequest`). A change of
the request builders touches this file only.

* `serverReceives_refresh`: when every device's `bundle-seal` opened status 255 and the controller
  built the `PUT /v1/messages/{uuid}` frame from the opened envelopes in device order
  (`buildDevices`), `bundle-request-ctr`'s outputs are the TLS record (`sealedRequest`) of the
  masked WebSocket frame of `devicesMessage` whose message list holds, device by device, the
  reference PreKey sealed-sender envelope `EstablishSeal.envelopeOf` of that device's seal inputs,
  with the contact's UUID, access key and each device's padded ids in their slots.
* `serverReceives_refresh_first`: the same for the first message after a refresh, with each
  device's envelope `EstablishFirst.Reference.firstEnvelope` of the key agreements, ids and keys of
  that device's `establish-session` run.

Trusted, not proved (as in RequestFrame.lean and SealFrame.lean): the C++ worker passes the opened
envelopes in device order and the controller's frame, mask and offsets unchanged (`built`,
`hframe`, `hmask`, `paired`), and wires each device's `establish-session` outputs into its
`bundle-seal` inputs (`EstablishDevices.wired`).
-/
namespace TlsMpc.KernelSpecs.EstablishRequest
open Std.Tactic.BVDecide
open TlsMpc TlsMpc.Signal
open TlsMpc.KernelSpecs.SealValue (Byte)
open TlsMpc.KernelSpecs.EstablishDevices (DeviceSeal DeviceSession firstOf wired openedEnvelopes_reference
  openedEnvelopes_first)
open PublicRequest (buildDevices devicesMessage total)
open TlsMpc.KernelSpecs.RequestFrame (assembleHeader maskFrom render devicesValues bundleRequestCtr_built)
open TlsMpc.HybridKernel (lookup)

/-- **The bytes the server receives for an accepted send to several unanswered devices.** -/
theorem serverReceives_refresh (cert content : Nat) (ds : List DeviceSeal)
    (hb : ∀ d ∈ ds, d.bounded cert content) (opened : ∀ d ∈ ds, (d.outputs cert content).getD 0 [] = [255])
    (timestamp id : Nat) (mask frame : List Byte) (official : Bool) (payloadAt : Nat) (offsets : List Nat)
    (built : buildDevices (ds.map (fun d => (d.outputs cert content).getD 3 [])) timestamp id mask official =
      .ok (frame, payloadAt, offsets))
    (devices : List (Nat × Nat)) (paired : BundleKernel.pairs (offsets.drop 2) = some devices)
    (assign : BVExpr.Assignment)
    (hframe : (lookup (requestInputsOf frame.length devices.length) "frame").map (BVExpr.eval assign) = frame)
    (hmask : (lookup (requestInputsOf frame.length devices.length) "mask").map (BVExpr.eval assign) = mask) :
    let get := fun name => (lookup (requestInputsOf frame.length devices.length) name).map (BVExpr.eval assign)
    let msg := devicesMessage (ds.map (fun d => d.reference cert content)) timestamp id official
    (BundleKernel.bundleRequestCtr frame.length payloadAt (offsets.getD 0 0) (offsets.getD 1 0) devices).outputs.map
        (fun field => field.value.map (BVExpr.eval assign)) =
      sealedRequest (get "clientApplication") (get "sequence")
        (assembleHeader (total msg) mask ++ maskFrom mask 0 (render (devicesValues (get "records")) msg))
        (bundleRequestValue (get "records") (offsets.getD 0 0) (offsets.getD 1 0) devices).1 := by
  rw [openedEnvelopes_reference cert content ds hb opened] at built
  exact bundleRequestCtr_built _ timestamp id mask frame official payloadAt offsets built devices paired assign
    hframe hmask

/-- **The first message after a refresh, as the server receives it**: each device's envelope is the
first PreKey sealed-sender message of the session its `establish-session` run set up. -/
theorem serverReceives_refresh_first (cert content : Nat) (ps : List (DeviceSession × DeviceSeal))
    (hb : ∀ p ∈ ps, p.2.bounded cert content) (hw : ∀ p ∈ ps, wired cert content p)
    (timestamp id : Nat) (mask frame : List Byte) (official : Bool) (payloadAt : Nat) (offsets : List Nat)
    (built : buildDevices (ps.map (fun p => (p.2.outputs cert content).getD 3 [])) timestamp id mask official =
      .ok (frame, payloadAt, offsets))
    (devices : List (Nat × Nat)) (paired : BundleKernel.pairs (offsets.drop 2) = some devices)
    (assign : BVExpr.Assignment)
    (hframe : (lookup (requestInputsOf frame.length devices.length) "frame").map (BVExpr.eval assign) = frame)
    (hmask : (lookup (requestInputsOf frame.length devices.length) "mask").map (BVExpr.eval assign) = mask) :
    let get := fun name => (lookup (requestInputsOf frame.length devices.length) name).map (BVExpr.eval assign)
    let msg := devicesMessage (ps.map (firstOf cert content)) timestamp id official
    (BundleKernel.bundleRequestCtr frame.length payloadAt (offsets.getD 0 0) (offsets.getD 1 0) devices).outputs.map
        (fun field => field.value.map (BVExpr.eval assign)) =
      sealedRequest (get "clientApplication") (get "sequence")
        (assembleHeader (total msg) mask ++ maskFrom mask 0 (render (devicesValues (get "records")) msg))
        (bundleRequestValue (get "records") (offsets.getD 0 0) (offsets.getD 1 0) devices).1 := by
  rw [openedEnvelopes_first cert content ps hb hw] at built
  exact bundleRequestCtr_built _ timestamp id mask frame official payloadAt offsets built devices paired assign
    hframe hmask

#print axioms serverReceives_refresh
#print axioms serverReceives_refresh_first

end TlsMpc.KernelSpecs.EstablishRequest
