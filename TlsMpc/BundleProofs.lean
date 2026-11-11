import TlsMpc.BundleKernels
import TlsMpc.ReceiveProofs

/-!
Theorems about the bundle kernels (`TlsMpc/BundleKernels.lean`).

PROVED (standard axioms only; no `sorry`, no `native_decide`):

* `compiled_correct`: for every kernel `find` returns, each exported gate-level
  output bit equals the corresponding bit of the kernel's Lean definition
  evaluated on the inputs. (The lowering to the flat gate list and the runtime
  are outside this statement.)
* `bundleShape_spec`, `bundleDevice_spec`, `bundleBind_spec`, `bundleSeal_spec`:
  on every input assignment, the kernel's output fields are the corresponding
  specification function (`TlsMpc/Signal/BundleResponse.lean`,
  `Establish.sealMessage`) on concrete bytes, applied to the values of the
  kernel's input fields.
* `device_rejects`, `bind_rejects`: when the validity is 0, every field of the
  stage is zero.
* What the per-character circuits compute, for all 256 bytes:
  `structural_value` (the opened flag is 255 exactly for `" , : [ ] { }`, so
  `shape` reveals nothing else about a byte), `digitValid_value`,
  `sextetValid_value`, `sextetValue_value` (the base64 alphabet and its values).
* `byteAt_value`: the three bytes of a group of four six-bit values are the
  base64 ones. With `sextetValue_value` this is the meaning of
  `BundleResponse.decode`, which is by definition `byteAt` over the characters'
  values.
* `layout?_sound`: when the controllers' `layout?` accepts the opened flags,
  they are exactly the punctuation flags of the response template for the
  widths it returns, and every width is within the bounds `find` requires.
* `shape_length`: the opened shape has one flag per body byte.

NOT PROVED, only tested (`handshake_backend/EmpHybridWork/check_bundle_kernels.py`,
against an independent Python reference):

* `number_spec` (not stated): that `numberBits` / `numberBytes` on a string of
  digits is its decimal value, and that `numberValid` accepts exactly the
  canonical decimals below `2^limit`. The ripple adder is
  `PrivateBuffer.addLoop`, whose arithmetic meaning is
  `PrivateBuffer.Semantics.addLoop_integer`; the Horner recurrence over it and
  the repacking into bytes are not proved. (An exhaustive kernel `decide` over
  the 1000 device ids exceeded the 8 GB guard and was removed.)
* that `decodeValid`'s check of the last character's unused bits is the
  canonical-encoding condition (it is two or four `maskBit`s; not stated as a
  theorem).
* that the template is what Signal-Server writes (read from its source; no
  server was run), and that `layout?` accepts every response the template
  describes (completeness; soundness is proved).
* No theorem is stated about `bundle-fetch-ctr` and `bundle-request-ctr` beyond
  `compiled_correct`, as for `signal-request-ctr`.

Nothing here is a security statement.
-/
namespace TlsMpc.BundleKernel
open Std.Tactic.BVDecide
open Signal
open HybridKernel (Kernel lookup sl)
open ReceiveKernel (values)

theorem compiled_correct (arguments : List String) (k : Kernel) (_found : find arguments = some k)
    (assign : BVExpr.Assignment) (index : Nat) (hi : index < 8 * k.bytes.length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr k.bytes)).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr k.bytes)).vec.get index hi)) =
    (ByteCircuit.joinValue (k.bytes.map (BVExpr.eval assign))).getLsbD index :=
  HybridKernel.compiled_correct k assign index hi

/-! ### Kernels as specification functions on values -/

theorem bundleShape_spec (size : Nat) (assign : BVExpr.Assignment) :
    values (bundleShape size) assign =
      BundleResponse.shape ByteAuth.concrete ((lookup (shapeInputs size) "body").map (BVExpr.eval assign)) := by
  rw [← BundleResponse.shape_map (ByteAuth.evaluationHom assign)]
  rfl

theorem bundleDevice_spec (size start : Nat) (w : BundleResponse.Widths) (assign : BVExpr.Assignment) :
    let out := BundleResponse.device ByteAuth.concrete size start w
      ((lookup (shapeInputs size) "body").map (BVExpr.eval assign))
    values (bundleDevice size start w) assign =
      [out.getD 0 [], out.getD 1 [], out.getD 2 [], out.getD 3 [], out.getD 4 [], out.getD 5 [], out.getD 6 [],
        out.getD 7 [], out.getD 8 [], out.getD 9 []] ++
      (if w.oneTime = 0 then [] else [out.getD 10 [], out.getD 11 []]) := by
  dsimp only
  by_cases none : w.oneTime = 0 <;>
    simp only [values, bundleDevice, HybridKernel.priv, none, if_true, if_false, List.map_cons, List.map_nil,
      List.map_append, List.append_nil, EstablishKernel.getD_map,
      BundleResponse.device_map (ByteAuth.evaluationHom assign)]

theorem bundleBind_spec (assign : BVExpr.Assignment) :
    let get := lookup bindInputs
    let e := BVExpr.eval assign
    values (bundleBind ()) assign =
      BundleResponse.bind ByteAuth.concrete ((get "record").map e) ((get "valid").map e) ((get "verified").map e)
        ((get "identityKey").map e) := by
  intro get e
  rw [← BundleResponse.bind_map (ByteAuth.evaluationHom assign)]
  rfl

theorem bundleSeal_spec (cert : Nat) (withOneTime : Bool)
    (content counterWidth previousWidth epochWidth indexWidth : Nat) (assign : BVExpr.Assignment) :
    let get := lookup (sealInputs cert content)
    let e := BVExpr.eval assign
    let record := get "conversation"
    let out := Establish.sealMessage Aes.concrete Varint64.concrete Sha256.concrete ByteAuth.concrete withOneTime
      ⟨counterWidth, previousWidth, true⟩ ⟨epochWidth, indexWidth, 0, false⟩ content ((sl record cert 262).map e)
      ((sl record (cert + 262) 57).map e) ((get "pending").map e) ((sl record 0 cert).map e)
      ((get "localAddress").map e) ((get "text").map e) ((get "ephemeralPublic").map e) ((get "senderPublic").map e)
      ((get "ephemeralAgreement").map e) ((get "staticAgreement").map e)
    values (bundleSeal cert withOneTime content counterWidth previousWidth epochWidth indexWidth) assign =
      [out.getD 0 [], (sl record 0 cert).map e ++ (out.getD 1 []).take 262 ++ (sl record (cert + 262) 57).map e,
        (sl (get "text") (2 + content) 8).map e, out.getD 2 []] := by
  dsimp only
  simp only [values, bundleSeal, HybridKernel.pub, HybridKernel.priv, List.map_cons, List.map_nil,
    List.map_append, List.map_take, EstablishKernel.getD_map, Establish.sealMessage_map (Aes.evaluationHom assign)
      (Varint64.evaluationHom assign) (Sha256Ripple.evaluationHom assign) (ByteAuth.evaluationHom assign)]

/-! ### A failed stage releases nothing -/

theorem device_rejects (total start : Nat) (w : BundleResponse.Widths) (body : List (BitVec 8))
    (failed : (BundleResponse.device ByteAuth.concrete total start w body).getD 0 [] = [0]) :
    ∀ field ∈ BundleResponse.device ByteAuth.concrete total start w body, ∀ byte ∈ field, byte = 0 := by
  obtain ⟨status, fields, shape⟩ : ∃ status, ∃ fields : List (List (BitVec 8)),
      BundleResponse.device ByteAuth.concrete total start w body =
      [status] :: fields.map (ByteAuth.release ByteAuth.concrete status) := ⟨_, _, rfl⟩
  rw [shape] at failed ⊢
  exact ReceiveKernel.released_zero status fields (by simpa using failed)

theorem bind_rejects (record valid verified identityKey : List (BitVec 8))
    (failed : (BundleResponse.bind ByteAuth.concrete record valid verified identityKey).getD 0 [] = [0]) :
    ∀ field ∈ BundleResponse.bind ByteAuth.concrete record valid verified identityKey, ∀ byte ∈ field, byte = 0 := by
  obtain ⟨status, fields, shape⟩ : ∃ status, ∃ fields : List (List (BitVec 8)),
      BundleResponse.bind ByteAuth.concrete record valid verified identityKey =
        [status] :: fields.map (ByteAuth.release ByteAuth.concrete status) := ⟨_, _, rfl⟩
  rw [shape] at failed ⊢
  exact ReceiveKernel.released_zero status fields (by simpa using failed)

/-! ### What the per-character circuits compute -/

/-- The base64 alphabet, in value order. -/
def alphabet : List Nat :=
  (List.range 26).map (65 + ·) ++ (List.range 26).map (97 + ·) ++ (List.range 10).map (48 + ·) ++ [43, 47]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The opened flag depends only on whether the byte is one of `" , : [ ] { }`. -/
theorem structural_value (c : BitVec 8) :
    BundleResponse.structural ByteAuth.concrete c = if c.toNat ∈ BundleResponse.punctuation then 255 else 0 := by
  have every : ∀ c : BitVec 8, BundleResponse.structural ByteAuth.concrete c =
      if c.toNat ∈ BundleResponse.punctuation then 255 else 0 := by decide +kernel
  exact every c

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem digitValid_value (c : BitVec 8) :
    BundleResponse.digitValid ByteAuth.concrete c = if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then 255 else 0 := by
  have every : ∀ c : BitVec 8, BundleResponse.digitValid ByteAuth.concrete c =
      if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then 255 else 0 := by decide +kernel
  exact every c

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sextetValid_value (c : BitVec 8) :
    BundleResponse.sextetValid ByteAuth.concrete c = if c.toNat ∈ alphabet then 255 else 0 := by
  have every : ∀ c : BitVec 8, BundleResponse.sextetValid ByteAuth.concrete c =
      if c.toNat ∈ alphabet then 255 else 0 := by decide +kernel
  exact every c

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The value of the `v`-th character of the alphabet is `v`. -/
theorem sextetValue_value (v : Nat) (inside : v < 64) :
    BundleResponse.sextetValue ByteAuth.concrete (BitVec.ofNat 8 (alphabet.getD v 0)) = BitVec.ofNat 8 v := by
  have every : ∀ v : Fin 64, BundleResponse.sextetValue ByteAuth.concrete (BitVec.ofNat 8 (alphabet.getD v.val 0)) =
      BitVec.ofNat 8 v.val := by decide +kernel
  exact every ⟨v, inside⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem slice_values (x : BitVec 8) :
    RelayEncoding.slice ByteAuth.concrete x 0 6 2 = (x &&& 63) <<< 2 ∧
    RelayEncoding.slice ByteAuth.concrete x 4 2 0 = (x >>> 4) &&& 3 ∧
    RelayEncoding.slice ByteAuth.concrete x 0 4 4 = (x &&& 15) <<< 4 ∧
    RelayEncoding.slice ByteAuth.concrete x 2 4 0 = (x >>> 2) &&& 15 ∧
    RelayEncoding.slice ByteAuth.concrete x 0 2 6 = (x &&& 3) <<< 6 ∧
    RelayEncoding.slice ByteAuth.concrete x 0 6 0 = x &&& 63 := by
  have every : ∀ x : BitVec 8,
      RelayEncoding.slice ByteAuth.concrete x 0 6 2 = (x &&& 63) <<< 2 ∧
      RelayEncoding.slice ByteAuth.concrete x 4 2 0 = (x >>> 4) &&& 3 ∧
      RelayEncoding.slice ByteAuth.concrete x 0 4 4 = (x &&& 15) <<< 4 ∧
      RelayEncoding.slice ByteAuth.concrete x 2 4 0 = (x >>> 2) &&& 15 ∧
      RelayEncoding.slice ByteAuth.concrete x 0 2 6 = (x &&& 3) <<< 6 ∧
      RelayEncoding.slice ByteAuth.concrete x 0 6 0 = x &&& 63 := by decide +kernel
  exact every x

/-- The three bytes of a group of four six-bit values `v 0 … v 3`, as base64
defines them: `v0·4 + v1/16`, `(v1 mod 16)·16 + v2/4`, `(v2 mod 4)·64 + v3`. -/
theorem byteAt_value (values : List (BitVec 8)) (q : Nat) :
    let v := fun i => OpenResult.get ByteAuth.concrete values (4 * q + i)
    BundleResponse.byteAt ByteAuth.concrete values (3 * q) = ((v 0 &&& 63) <<< 2) ^^^ ((v 1 >>> 4) &&& 3) ∧
    BundleResponse.byteAt ByteAuth.concrete values (3 * q + 1) = ((v 1 &&& 15) <<< 4) ^^^ ((v 2 >>> 2) &&& 15) ∧
    BundleResponse.byteAt ByteAuth.concrete values (3 * q + 2) = ((v 2 &&& 3) <<< 6) ^^^ (v 3 &&& 63) := by
  intro v
  have m0 : (3 * q) % 3 = 0 := by omega
  have d0 : (3 * q) / 3 = q := by omega
  have n1 : ¬ (3 * q + 1) % 3 = 0 := by omega
  have m1 : (3 * q + 1) % 3 = 1 := by omega
  have d1 : (3 * q + 1) / 3 = q := by omega
  have n2 : ¬ (3 * q + 2) % 3 = 0 := by omega
  have k2 : ¬ (3 * q + 2) % 3 = 1 := by omega
  have d2 : (3 * q + 2) / 3 = q := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [BundleResponse.byteAt, if_pos m0, d0, (slice_values _).1, (slice_values _).2.1]
    rfl
  · rw [BundleResponse.byteAt, if_neg n1, if_pos m1, d1, (slice_values _).2.2.1, (slice_values _).2.2.2.1]
    rfl
  · rw [BundleResponse.byteAt, if_neg n2, if_neg k2, d2, (slice_values _).2.2.2.2.1, (slice_values _).2.2.2.2.2]
    rfl

/-! ### The opened shape and the layout -/

theorem shape_length (body : List (BitVec 8)) :
    ((BundleResponse.shape ByteAuth.concrete body).getD 0 []).length = body.length := by
  simp [BundleResponse.shape]

/-- An accepted layout is exactly the template's: the opened flags are the
punctuation flags of `response ws`, and the widths are within bounds. -/
theorem layout?_sound (mask : List Bool) (ws : List BundleResponse.Widths)
    (accepted : BundleResponse.layout? mask = some ws) :
    BundleResponse.maskOf (BundleResponse.response ws) = mask ∧ ws.all BundleResponse.Widths.ok = true := by
  unfold BundleResponse.layout? at accepted
  dsimp only at accepted
  split at accepted
  · rename_i holds
    obtain rfl := Option.some.inj accepted
    rw [Bool.and_eq_true] at holds
    exact ⟨by simpa using holds.2, holds.1⟩
  · cases accepted

#print axioms compiled_correct
#print axioms bundleShape_spec
#print axioms bundleDevice_spec
#print axioms bundleBind_spec
#print axioms bundleSeal_spec
#print axioms device_rejects
#print axioms bind_rejects
#print axioms structural_value
#print axioms digitValid_value
#print axioms sextetValid_value
#print axioms sextetValue_value
#print axioms byteAt_value
#print axioms shape_length
#print axioms layout?_sound

end TlsMpc.BundleKernel
