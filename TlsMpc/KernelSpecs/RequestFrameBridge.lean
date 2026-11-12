import TlsMpc.KernelSpecs.RequestFrame
import handshake_backend.EmpHybridWork.PublicServiceController

/-!
# The restated request builders are the controller's (bridge; NOT imported by `Security.lean`)

`TlsMpc/KernelSpecs/RequestFrame.lean` proves its theorems about `RequestFrame.Mirror.build`,
`buildFetch` and `buildDevices`, restatements of `PublicRequest.*` from the controller's executable
root (which `TlsMpc/Security.lean` does not import). This file imports that root and proves the
restatements equal to the controller's functions, with `PublicReceive.fast` for the byte
operations:

* `build_bridge`: `PublicRequest.build = Mirror.build PublicReceive.fast`;
* `buildFetch_bridge`: `PublicRequest.buildFetch = Mirror.buildFetch`;
* `buildDevices_bridge`: `PublicRequest.buildDevices = Mirror.buildDevices PublicReceive.fast`.

It is checked on its own (`lake env lean TlsMpc/KernelSpecs/RequestFrameBridge.lean`, against the
controller's current `.olean`); a change to `PublicRequest` breaks it. No emitter imports it.
-/
namespace TlsMpc.KernelSpecs.RequestFrame.Bridge
open TlsMpc TlsMpc.Signal
open RequestFrame.Mirror (Piece total)

def tr : PublicRequest.Piece → Piece
  | .bytes v => .bytes v
  | .slot i w => .slot i w

theorem total_tr (ps : List PublicRequest.Piece) : Mirror.total (ps.map tr) = PublicRequest.total ps := by
  unfold Mirror.total PublicRequest.total
  rw [List.map_map]
  congr 2
  funext p
  cases p <;> rfl

theorem field_tr (tag : Nat) (ps : List PublicRequest.Piece) :
    (PublicRequest.field tag ps).map tr = Mirror.field tag (ps.map tr) := by
  simp only [PublicRequest.field, Mirror.field, List.map_cons, total_tr]
  rfl

theorem text_eq (s : String) : PublicRequest.text s = Mirror.text s := rfl
theorem varint_eq (n : Nat) : PublicRequest.varint n = Mirror.varint n := rfl

theorem officialJson_tr (envelopes : List (List (BitVec 8))) (timestamp : Nat) :
    (PublicRequest.officialJson envelopes timestamp).map tr = Mirror.officialJson PublicReceive.fast envelopes timestamp := by
  simp only [PublicRequest.officialJson, Mirror.officialJson, List.map_append, List.map_cons, List.map_nil,
    List.map_flatten, List.map_map, Function.comp_def, text_eq]
  rfl

/-- The controller's `build`, through the same loop lemma as `RequestFrame.build_eq`. -/
def stepC (mask : List (BitVec 8)) (piece : PublicRequest.Piece) (r : MProd (List (BitVec 8)) (Array Nat)) :
    MProd (List (BitVec 8)) (Array Nat) := stepB mask (tr piece) r

theorem build_bridge (envelope : List (BitVec 8)) (timestamp id : Nat) (mask : List (BitVec 8)) (official : Bool) :
    PublicRequest.build envelope timestamp id mask official =
      Mirror.build PublicReceive.fast envelope timestamp id mask official := by
  rw [build_eq]
  unfold PublicRequest.build
  simp only [pure_bind, bind_pure_comp, map_pure]
  generalize hm : sendMessage PublicReceive.fast envelope timestamp id official = m
  have hc : (PublicRequest.Piece.bytes [8, 1] :: PublicRequest.field 18
      (PublicRequest.field 10 [.bytes (PublicRequest.text "PUT")] ++
        PublicRequest.field 18 ([.bytes (PublicRequest.text "/v1/messages/"), .slot 0 36] ++
          (if official then [] else [.bytes (PublicRequest.text "?story=false")])) ++
        PublicRequest.field 26 (if official then PublicRequest.officialJson [envelope] timestamp else [
          .bytes (PublicRequest.text "{\"messages\":[{\"content\":\"" ++ RelayEncoding.base64 PublicReceive.fast envelope ++
            PublicRequest.text "\",\"destinationDeviceId\":"), .slot 2 3,
          .bytes (PublicRequest.text ",\"destinationRegistrationId\":"), .slot 3 10,
          .bytes (PublicRequest.text (",\"type\":6}],\"online\":false,\"timestamp\":" ++ toString timestamp ++
            ",\"urgent\":true}"))]) ++
        [.bytes (32 :: PublicRequest.varint id)] ++
        PublicRequest.field 42 [.bytes (PublicRequest.text "content-type: application/json")] ++
        PublicRequest.field 42 [.bytes (PublicRequest.text "unidentified-access-key: "), .slot 1 24])).map tr = m := by
    rw [← hm]
    cases official <;>
      simp [sendMessage, field_tr, officialJson_tr, text_eq, varint_eq, List.map_append, tr, Mirror.field]
  generalize hC : (PublicRequest.Piece.bytes [8, 1] :: PublicRequest.field 18
      (PublicRequest.field 10 [.bytes (PublicRequest.text "PUT")] ++
        PublicRequest.field 18 ([.bytes (PublicRequest.text "/v1/messages/"), .slot 0 36] ++
          (if official then [] else [.bytes (PublicRequest.text "?story=false")])) ++
        PublicRequest.field 26 (if official then PublicRequest.officialJson [envelope] timestamp else [
          .bytes (PublicRequest.text "{\"messages\":[{\"content\":\"" ++ RelayEncoding.base64 PublicReceive.fast envelope ++
            PublicRequest.text "\",\"destinationDeviceId\":"), .slot 2 3,
          .bytes (PublicRequest.text ",\"destinationRegistrationId\":"), .slot 3 10,
          .bytes (PublicRequest.text (",\"type\":6}],\"online\":false,\"timestamp\":" ++ toString timestamp ++
            ",\"urgent\":true}"))]) ++
        [.bytes (32 :: PublicRequest.varint id)] ++
        PublicRequest.field 42 [.bytes (PublicRequest.text "content-type: application/json")] ++
        PublicRequest.field 42 [.bytes (PublicRequest.text "unidentified-access-key: "), .slot 1 24])) = c at hc
  subst hc
  have ht : PublicRequest.total c = total (c.map tr) := (total_tr c).symm
  rw [ht]
  by_cases h : (decide (126 ≤ total (c.map tr)) && decide (total (c.map tr) < 65536) && mask.length == 4) = true
  · rw [if_pos h, if_pos h]
    have h4 : mask.length = 4 := by simp at h; exact h.2
    rw [forIn_eq_foldl' _ _ _ (stepC mask) (by
      intro piece r; cases piece <;> simp [stepC, stepB, tr, map_pure, List.forIn_pure_yield_eq_foldl])]
    obtain ⟨f1, f2⟩ := foldB mask (c.map tr) (buildHeader (total (c.map tr)) mask) #[0, 0, 0, 0] (by simp [buildHeader, h4])
    have len : (buildHeader (total (c.map tr)) mask).length = 8 := by simp [buildHeader, h4]
    rw [len, List.foldl_map] at f1 f2
    simp only [buildHeader, map_pure, Nat.sub_self] at f1 f2 ⊢
    simp only [stepC]
    rw [f1, f2]
    rfl
  · rw [if_neg h, if_neg h]
    rfl

theorem assemble_bridge (message : List PublicRequest.Piece) (mask : List (BitVec 8)) (slots : Nat) :
    PublicRequest.assemble message mask slots = Mirror.assemble (message.map tr) mask slots := by
  rw [assemble_eq]
  unfold PublicRequest.assemble
  simp only [pure_bind, bind_pure_comp, map_pure]
  have ht : PublicRequest.total message = total (message.map tr) := (total_tr message).symm
  rw [ht]
  by_cases h : (decide (0 < total (message.map tr)) && decide (total (message.map tr) < 65536) && mask.length == 4) = true
  · rw [if_pos h, if_pos h]
    rw [forIn_eq_foldl' _ _ _ (fun piece r => stepA (assembleHeader (total (message.map tr)) mask).length mask (tr piece) r)
      (by intro piece r; cases piece <;> simp [stepA, tr, map_pure, List.forIn_pure_yield_eq_foldl, assembleHeader])]
    obtain ⟨f1, f2⟩ := foldA (assembleHeader (total (message.map tr)) mask).length mask (message.map tr)
      (assembleHeader (total (message.map tr)) mask).toArray (Array.replicate slots 0) (by simp)
    rw [List.foldl_map] at f1 f2
    simp only [List.size_toArray, Nat.sub_self] at f1 f2
    simp only [assembleHeader, map_pure] at f1 f2 ⊢
    rw [f1, f2]
    rfl
  · rw [if_neg h, if_neg h]
    rfl

theorem buildFetch_bridge (id : Nat) (mask : List (BitVec 8)) :
    PublicRequest.buildFetch id mask = Mirror.buildFetch id mask := by
  unfold PublicRequest.buildFetch
  rw [assemble_bridge, buildFetch_eq]
  congr 1

theorem buildDevices_bridge (envelopes : List (List (BitVec 8))) (timestamp id : Nat) (mask : List (BitVec 8))
    (official : Bool) :
    PublicRequest.buildDevices envelopes timestamp id mask official =
      Mirror.buildDevices PublicReceive.fast envelopes timestamp id mask official := by
  rw [buildDevices_eq]
  unfold PublicRequest.buildDevices
  cases e : envelopes.isEmpty
  · simp only [Bool.not_false, Bool.false_eq_true, if_true, if_false, pure_bind]
    rw [assemble_bridge]
    congr 1
    cases official <;>
      simp [devicesMessage, field_tr, officialJson_tr, text_eq, varint_eq, List.map_append, tr, Mirror.field,
        List.map_flatten, List.map_map, Function.comp_def]
  · simp only [Bool.not_true, Bool.false_eq_true, if_true, if_false]
    rfl

#print axioms build_bridge
#print axioms buildFetch_bridge
#print axioms buildDevices_bridge

end TlsMpc.KernelSpecs.RequestFrame.Bridge
