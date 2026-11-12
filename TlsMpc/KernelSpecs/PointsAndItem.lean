import TlsMpc.BundleProofs
import TlsMpc.BundleItemKernels

/-!
Kernel-level specifications of `establish-points` (`EstablishKernel.establishPoints`) and
`bundle-item` (`BundleItemKernel.bundleItem`).

New file; it changes no definition and no emitter imports it.

PROVED (standard axioms only; no `sorry`, `native_decide`, `bv_decide`):

* `establishPoints_spec`: the outputs are the identity key, the signed prekey and (with a
  one-time prekey) the one-time prekey bytes, unchanged. (Each output declares `bits := 255`,
  so only the low 255 bits go to the field engine; this value statement does not cover that.)
* `bundleItem_spec`: on every input assignment, the outputs are `BundleResponse.device` on
  concrete bytes, applied to the body `head ‖ before ‖ item ‖ after ‖ end` built from the
  kernel's input fields, at the item's start (as `bundleSlot_spec` for `bundle-slot`).
* `bundleItem_rejects`: when `valid` is 0, every output is zero (from
  `BundleKernel.device_rejects`).

NOT PROVED: that `device` on the reassembled body equals `device` on the whole response body
at the item's offset (SECURITY_MAP C.2: "no theorem links them"). That needs a locality lemma
for `BundleResponse.device` (it reads only the header, the item, its two neighbours and the
last two bytes), which is not stated anywhere.
-/
namespace TlsMpc.KernelSpecs.PointsAndItem
open Std.Tactic.BVDecide
open Signal
open HybridKernel (Kernel Shape lookup)
open ReceiveKernel (values)

def pointsInputs (withOneTime : Bool) : List (String × Shape) :=
  [("identityKey", Shape.bytes 32), ("signedPrekey", .bytes 32)] ++
    (if withOneTime then [("oneTimePrekey", Shape.bytes 32)] else [])

theorem establishPoints_spec (withOneTime : Bool) (assign : BVExpr.Assignment) :
    let get := fun name => (lookup (pointsInputs withOneTime) name).map (BVExpr.eval assign)
    values (EstablishKernel.establishPoints withOneTime) assign =
      [get "identityKey", get "signedPrekey"] ++ (if withOneTime then [get "oneTimePrekey"] else []) := by
  intro get
  cases withOneTime <;> rfl

theorem bundleItem_spec (first last : Bool) (w : BundleResponse.Widths) (assign : BVExpr.Assignment) :
    let get := fun name => (lookup (BundleItemKernel.itemInputs first last w) name).map (BVExpr.eval assign)
    let body := get "head" ++ get "before" ++ get "item" ++ get "after" ++ get "end"
    let out := BundleResponse.device ByteAuth.concrete body.length
      (BundleResponse.firstItem + (if first then 0 else 1)) w body
    values (BundleItemKernel.bundleItem first last w) assign =
      [out.getD 0 [], out.getD 1 [], out.getD 2 [], out.getD 3 [], out.getD 4 [], out.getD 5 [], out.getD 6 [],
        out.getD 7 [], out.getD 8 [], out.getD 9 []] ++
      (if w.oneTime = 0 then [] else [out.getD 10 [], out.getD 11 []]) := by
  dsimp only
  by_cases none : w.oneTime = 0 <;>
    simp only [values, BundleItemKernel.bundleItem, HybridKernel.priv, none, if_true, if_false, List.map_cons,
      List.map_nil, List.map_append, List.append_nil, List.length_map, List.length_append, EstablishKernel.getD_map,
      BundleResponse.device_map (ByteAuth.evaluationHom assign)]

theorem bundleItem_rejects (first last : Bool) (w : BundleResponse.Widths) (assign : BVExpr.Assignment)
    (failed : (values (BundleItemKernel.bundleItem first last w) assign).getD 0 [] = [0]) :
    ∀ field ∈ values (BundleItemKernel.bundleItem first last w) assign, ∀ byte ∈ field, byte = 0 := by
  rw [bundleItem_spec] at failed ⊢
  dsimp only at failed ⊢
  generalize hout : BundleResponse.device ByteAuth.concrete _ _ w _ = out at failed ⊢
  have all := BundleKernel.device_rejects _ _ w _ (by rw [hout]; simpa using failed)
  rw [hout] at all
  have member : ∀ i, (out.getD i []) = [] ∨ out.getD i [] ∈ out := by
    intro i
    rw [List.getD_eq_getElem?_getD]
    cases h : out[i]? with
    | none => left; rfl
    | some x => right; exact List.mem_of_getElem? h
  intro field inField byte inByte
  have pick : ∃ i, field = out.getD i [] := by
    by_cases none : w.oneTime = 0
    · simp only [none, if_true, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at inField
      rcases inField with h | h | h | h | h | h | h | h | h | h <;> exact ⟨_, h⟩
    · simp only [none, if_false, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at inField
      rcases inField with (h | h | h | h | h | h | h | h | h | h) | (h | h) <;> exact ⟨_, h⟩
  obtain ⟨i, rfl⟩ := pick
  rcases member i with empty | inside
  · rw [empty] at inByte
    cases inByte
  · exact all _ inside byte inByte

#print axioms establishPoints_spec
#print axioms bundleItem_spec
#print axioms bundleItem_rejects

end TlsMpc.KernelSpecs.PointsAndItem
