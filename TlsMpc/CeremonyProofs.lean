import TlsMpc.CeremonyKernels
import TlsMpc.ReceiveProofs

/-!
Theorems about the ceremony kernels (`TlsMpc/CeremonyKernels.lean`).

PROVED (standard axioms only; no `sorry`, no `native_decide`):

* `compiled_correct`: for every kernel `find` returns, each exported gate-level output bit equals
  the corresponding bit of the kernel's Lean definition evaluated on the inputs.
* `ceremonySecrets_spec`: on every input assignment the three output fields of `ceremony-secrets`
  are `Ceremony.secrets` on concrete bytes applied to the values of its inputs: the password is
  the first 22 characters of base64 of the XOR of the two seeds, the recovery password the XOR of
  the two halves, and the one opened field the password XOR both masks.
* `masked_hides`: for bytes, XOR with a mask is a bijection of the mask (the opened byte equals
  any given value for exactly one value of the other node's mask byte). Per byte; the statement
  that a uniform mask therefore makes `masked` independent of the password is not formalised.
* `registerPlaintext_spec`: the plaintext `ceremony-register-ctr` encrypts is `Ceremony.fill`
  on concrete bytes: the frame, with base64 of (tail, password) and base64 of the recovery
  password written into the two slots under the WebSocket mask.

NOT PROVED, only tested (the ceremony against the local server; the server accepts the request
and then the password the shares combine to):

* that `RelayEncoding.base64` is RFC 4648 base64, and that base64 of `NUMBER:PASSWORD` is the
  public prefix followed by the slot (`Ceremony.basicConsistent` is evaluated by the controllers
  on the number in use, with a stand-in password, before the request is built);
* that `fill` leaves every byte outside the slots as the controllers built it (it does, by
  definition: the `none` branch) and that slots do not overlap (`BundleKernel.slotsOk`, checked
  by `find`);
* the encryption around the plaintext (`TlsRecord.inner`, `Gcm.ctr`), as for the other request
  kernels; the request text of `TlsMpc/CeremonyRequests.lean` against the server's parser.

Nothing here is a security statement.
-/
namespace TlsMpc.Ceremony
open Signal

section Refinement
variable {a : ByteAuth.Ops B} {b : ByteAuth.Ops B'} {f : B → B'} (h : ByteAuth.Hom a b f)
include h

theorem xor_map (xs ys : List B) :
    (List.zipWith a.xor xs ys).map f = List.zipWith b.xor (xs.map f) (ys.map f) := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys => simp [h.xor, ih]

theorem password_map (seedA seedB : List B) :
    (password a seedA seedB).map f = password b (seedA.map f) (seedB.map f) := by
  simp only [password, List.map_take, RelayEncoding.base64_map h, xor_map h]

theorem secrets_map (seedA seedB maskA maskB recoveryA recoveryB : List B) :
    (secrets a seedA seedB maskA maskB recoveryA recoveryB).map (List.map f) =
      secrets b (seedA.map f) (seedB.map f) (maskA.map f) (maskB.map f) (recoveryA.map f) (recoveryB.map f) := by
  simp only [secrets, List.map_cons, List.map_nil, password_map h, xor_map h]

omit h in
theorem getD_map' (values : List B) (index : Nat) (zero : B) :
    f (values.getD index zero) = (values.map f).getD index (f zero) := by
  induction values generalizing index with
  | nil => rfl
  | cons x xs ih => cases index with
    | zero => rfl
    | succ n => simpa using ih n

omit h in
theorem slotAt_map (zero : B) (slots : List (Nat × List B)) (index : Nat) :
    (slotAt zero slots index).map f = slotAt (f zero) (slots.map (fun slot => (slot.1, slot.2.map f))) index := by
  induction slots with
  | nil => rfl
  | cons slot rest ih =>
    simp only [slotAt, List.map_cons, List.findSome?_cons, List.length_map] at ih ⊢
    by_cases inside : (slot.1 ≤ index && index < slot.1 + slot.2.length) = true
    · simp [inside, getD_map']
    · simpa [inside] using ih

theorem registerSlots_map (secrets : List B) (tail authAt recoveryAt : Nat) :
    (registerSlots a secrets tail authAt recoveryAt).map (fun slot => (slot.1, slot.2.map f)) =
      registerSlots b (secrets.map f) tail authAt recoveryAt := by
  simp only [registerSlots, List.map_cons, List.map_nil, RelayEncoding.base64_map h, List.map_take, List.map_drop]

theorem fill_map (frame mask : List B) (payloadAt : Nat) (slots : List (Nat × List B)) :
    (fill a frame mask payloadAt slots).map f =
      fill b (frame.map f) (mask.map f) payloadAt (slots.map (fun slot => (slot.1, slot.2.map f))) := by
  unfold fill
  rw [List.map_map, List.zipIdx_map, List.map_map]
  apply List.map_congr_left
  intro pair _
  simp only [Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq]
  rw [← h.const 0, ← slotAt_map]
  cases slotAt (a.const 0) slots pair.2 with
  | none => rfl
  | some secret => simp [h.xor, getD_map']

end Refinement

/-- The opened byte takes a given value for exactly one value of a mask byte. -/
theorem masked_hides (word other value : BitVec 8) :
    ∃ mask : BitVec 8, word ^^^ (other ^^^ mask) = value ∧ ∀ m : BitVec 8, word ^^^ (other ^^^ m) = value → m = mask := by
  refine ⟨word ^^^ other ^^^ value, ?_, ?_⟩
  · ext i hi
    simp only [BitVec.getElem_xor]
    cases word[i] <;> cases other[i] <;> cases value[i] <;> rfl
  · intro m hm
    rw [← hm]
    ext i hi
    simp only [BitVec.getElem_xor]
    cases word[i] <;> cases other[i] <;> cases m[i] <;> rfl

end TlsMpc.Ceremony

namespace TlsMpc.CeremonyKernel
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

theorem ceremonySecrets_spec (assign : BVExpr.Assignment) :
    let get := lookup secretsInputs
    let e := BVExpr.eval assign
    values (ceremonySecrets ()) assign =
      Ceremony.secrets ByteAuth.concrete ((get "seedA").map e) ((get "seedB").map e) ((get "maskA").map e)
        ((get "maskB").map e) ((get "recoveryA").map e) ((get "recoveryB").map e) := by
  intro get e
  rw [← Ceremony.secrets_map (ByteAuth.evaluationHom assign)]
  rfl

theorem registerPlaintext_spec (size payloadAt authAt tail recoveryAt : Nat) (assign : BVExpr.Assignment) :
    let get := lookup (registerInputs size tail)
    let e := BVExpr.eval assign
    (registerPlaintext size payloadAt authAt tail recoveryAt).map e =
      Ceremony.fill ByteAuth.concrete ((get "frame").map e) ((get "mask").map e) payloadAt
        (Ceremony.registerSlots ByteAuth.concrete ((get "secrets").map e) tail authAt recoveryAt) := by
  intro get e
  rw [← Ceremony.registerSlots_map (ByteAuth.evaluationHom assign), ← Ceremony.fill_map (ByteAuth.evaluationHom assign)]
  rfl

end TlsMpc.CeremonyKernel
