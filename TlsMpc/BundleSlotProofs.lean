import TlsMpc.BundleSlotKernels
import TlsMpc.BundleProofs

/-!
Theorems about `bundle-slot` (`TlsMpc/BundleSlotKernels.lean`).

PROVED (standard axioms only; no `sorry`, no `native_decide`, no `bv_decide`):

* `compiled_correct`: each exported gate-level output bit of a kernel `find` returns equals the
  corresponding bit of the kernel's Lean definition evaluated on the inputs.
* `bundleSlot_spec`: on every input assignment, the kernel's outputs are
  `BundleSlots.deviceSlots` on concrete bytes, applied to the values of its input fields
  (the response made of `head`, `before`, `item`, `after`, `end`, and the digit counts `widths`).
* `slot_rejects`: when the validity is 0, every output is zero.

Proved since in `TlsMpc/KernelSpecs/BundleSlotWhole.lean` (restated in `TlsMpc/Security.lean`
section 2d): `deviceSlots` on the spliced item gives exactly `BundleResponse.device` on the
original (`deviceSlots_splice`, `slotValid_pad`), `BundleSlots.splice` produces the slot layout
(`spliced_layout`), and so `bundle-slot` on the body the server sent computes `device`
(`bundleSlot_device`); with the caveat `inconsistent_width_accepts` there (a `widths` input that
disagrees with the splice, on a number with a leading zero). `check_bundle_slots.py` remains as a
test. What `numberBytes`/`decode` mean as integers is `number_spec` in `TlsMpc/BundleProofs.lean`.
-/
namespace TlsMpc.BundleSlotKernel
open Std.Tactic.BVDecide
open Signal
open HybridKernel (Kernel lookup)
open ReceiveKernel (values)

theorem compiled_correct (arguments : List String) (k : Kernel) (_found : find arguments = some k)
    (assign : BVExpr.Assignment) (index : Nat) (hi : index < 8 * k.bytes.length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr k.bytes)).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr k.bytes)).vec.get index hi)) =
    (ByteCircuit.joinValue (k.bytes.map (BVExpr.eval assign))).getLsbD index :=
  HybridKernel.compiled_correct k assign index hi

theorem bundleSlot_spec (first last oneTime : Bool) (assign : BVExpr.Assignment) :
    let get := fun name => (lookup (slotInputs first last oneTime) name).map (BVExpr.eval assign)
    let body := get "head" ++ get "before" ++ get "item" ++ get "after" ++ get "end"
    let out := BundleSlots.deviceSlots ByteAuth.concrete body.length
      (BundleResponse.firstItem + (if first then 0 else 1)) oneTime (get "widths") body
    values (bundleSlot first last oneTime) assign =
      [out.getD 0 [], out.getD 1 [], out.getD 2 [], out.getD 3 [], out.getD 4 [], out.getD 5 [], out.getD 6 [],
        out.getD 7 [], out.getD 8 [], out.getD 9 []] ++
      (if oneTime then [out.getD 10 [], out.getD 11 []] else []) := by
  dsimp only
  cases oneTime <;>
    simp only [values, bundleSlot, HybridKernel.priv, if_true, if_false, Bool.false_eq_true, List.map_cons, List.map_nil,
      List.map_append, List.append_nil, List.length_map, List.length_append, EstablishKernel.getD_map,
      BundleSlots.deviceSlots_map (ByteAuth.evaluationHom assign)]

theorem slot_rejects (total start : Nat) (oneTime : Bool) (widths body : List (BitVec 8))
    (failed : (BundleSlots.deviceSlots ByteAuth.concrete total start oneTime widths body).getD 0 [] = [0]) :
    ∀ field ∈ BundleSlots.deviceSlots ByteAuth.concrete total start oneTime widths body, ∀ byte ∈ field, byte = 0 := by
  obtain ⟨status, fields, shape⟩ : ∃ status, ∃ fields : List (List (BitVec 8)),
      BundleSlots.deviceSlots ByteAuth.concrete total start oneTime widths body =
      [status] :: fields.map (ByteAuth.release ByteAuth.concrete status) := ⟨_, _, rfl⟩
  rw [shape] at failed ⊢
  exact ReceiveKernel.released_zero status fields (by simpa using failed)

#print axioms compiled_correct
#print axioms bundleSlot_spec
#print axioms slot_rejects

end TlsMpc.BundleSlotKernel
