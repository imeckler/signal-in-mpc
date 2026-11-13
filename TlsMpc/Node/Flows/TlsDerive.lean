import TlsMpc.Node.Flows.TlsOpenRun

/-!
# `deriveScript`'s value through the script (gap F15)

REORGANIZATION_PLAN.md stage S12. `tls-derive` has a `.word` input (the X25519 agreement as a 255-bit
field word, S11's `Curve.agree`), which `Contacts.kernelCircuit` / `TlsBase.circuitOf` (byte inputs
only) do not cover. The send stage (S13, `Flows/SendProofs.lean` on its branch) introduced the
model circuit `shapedCircuit K marks` that reads a kernel's bundle field by field (`.bytes k`: `8k`
bits; `.word`: 255 bits, one variable); the minimum needed here is re-created below under the
`Tls` namespace (`packs`, `shapedAssign`, `shapedOut`, `shapedCircuit`; same definitions, so the
two coincide when the branches join). An environment loading `shapedCircuit tlsDerive _` under the
name `tls-derive` is T2's trust, as for every kernel.

  * `agreementBytes`: the 32 little-endian bytes the kernel's body sees for the word (`wordBytes`:
    the word zero-extended to 256 bits, byte by byte).
  * `derive_out`: on the bundle `deriveScript` builds (agreement word ‖ hello hash), the kernel
    outputs the client and server handshake traffic blocks and the main secret of
    `TlsKdf.handshakeSecrets` (RFC 8446 key schedule without PSK) on those bytes and the hash
    (`tlsDerive_spec` through the script's layout).
  * **`derive_honest`**: two honest parties run `deriveScript` with the agreement word behind its
    handle; the run returns the three handles, which hold exactly the client handshake block, the
    server handshake block and the main secret; the agreement handle is freed.

No I/O; no emitter imports this module.
-/

namespace TlsMpc.Node.Flows.Tls

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts
open TlsMpc.Node.Flows.TlsBase
open TlsMpc.Node.Flows.Run
open Std.Tactic.BVDecide
open TlsMpc.HybridKernel (Kernel lookup lookupFrom)
open TlsMpc.KernelSpecs.TlsHandshake (trafficBlockValue deriveInputs)

/-! ## Model circuits for kernels with word inputs (as S13's `Send.shapedCircuit`) -/

/-- One packed variable per byte. -/
def pack8 (b : BitVec 8) : BVExpr.PackedBitVec := ⟨b⟩

/-- The kernel's variables from its input bundle: a bytes field one 8-bit variable per byte, a
word one 255-bit variable. -/
def packs : List (String × HybridKernel.Shape) → Bits → List BVExpr.PackedBitVec
  | [], _ => []
  | (_, .bytes k) :: rest, v => (bytesOf (v.take (8 * k))).map pack8 ++ packs rest (v.drop (8 * k))
  | (_, .word) :: rest, v => ⟨BitVec.ofBoolListLE (v.take 255)⟩ :: packs rest (v.drop 255)

def shapedAssign (inputs : List (String × HybridKernel.Shape)) (v : Bits) : BVExpr.Assignment :=
  chain 0 (packs inputs v)

/-- The kernel's output fields on the input bundle `v`, concatenated. -/
def shapedOut (K : Kernel) (v : Bits) : B8 :=
  (K.outputs.map fun f => f.value.map (BVExpr.eval (shapedAssign K.inputs v))).flatten

/-- The model circuit of a kernel with word inputs. -/
def shapedCircuit (K : Kernel) (marks : List Mark) : Engine.Circuit where
  inWidth := (K.inputs.map (·.2.bits)).sum
  outMarks := marks
  eval v := bitsOf (shapedOut K v)

/-! ## `tls-derive` on the script's bundle -/

/-- The 32 little-endian bytes the kernel's body sees for a 255-bit word (`HybridKdf.wordBytes`). -/
def agreementBytes (aw : Bits) : B8 :=
  (List.range 32).map fun i => BitVec.extractLsb' (8 * i) 8 ((0 : BitVec 1) ++ (BitVec.ofBoolListLE aw).truncate 255)

theorem derive_inputs : HybridKernel.tlsDerive.inputs = deriveInputs := rfl

theorem derive_assign (aw : Bits) (H : B8) (haw : aw.length = 255) (hH : H.length = 32) :
    shapedAssign HybridKernel.tlsDerive.inputs (aw ++ bitsOf H) = chain 0 (⟨BitVec.ofBoolListLE aw⟩ :: H.map pack8) := by
  have h8 : (bitsOf H).length = 8 * 32 := by rw [length_bitsOf, hH]
  unfold shapedAssign
  rw [derive_inputs]
  show chain 0 (⟨BitVec.ofBoolListLE ((aw ++ bitsOf H).take 255)⟩ ::
    ((bytesOf (((aw ++ bitsOf H).drop 255).take (8 * 32))).map pack8 ++
      packs [] (((aw ++ bitsOf H).drop 255).drop (8 * 32)))) = _
  rw [List.take_left' haw, List.drop_left' haw, List.take_of_length_le (Nat.le_of_eq h8), bytesOf_bitsOf]
  simp only [packs, List.append_nil]

theorem derive_get_agreement (aw : Bits) (rest : List BVExpr.PackedBitVec) :
    (lookup deriveInputs "agreement").map (BVExpr.eval (chain 0 (⟨BitVec.ofBoolListLE aw⟩ :: rest))) =
      agreementBytes aw := by
  have hl : lookup deriveInputs "agreement" = HybridKdf.wordBytes (.var 0) := by
    simp [lookup, lookupFrom, deriveInputs]
  rw [hl]
  simp only [HybridKdf.wordBytes, agreementBytes, List.map_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, BVExpr.eval_extract, BVExpr.eval_append, BVExpr.eval_var, BVExpr.eval_const]
  rw [get_chain _ 0 0 (Nat.le_refl 0)]
  rfl

theorem derive_get_hash (w : BVExpr.PackedBitVec) (H : B8) (hH : H.length = 32) :
    (lookup deriveInputs "helloHash").map (BVExpr.eval (chain 0 (w :: H.map pack8))) = H := by
  have hl : lookup deriveInputs "helloHash" = ByteCircuit.inputBytes 1 32 := by
    simp [lookup, lookupFrom, deriveInputs, HybridKernel.Shape.variables]
  rw [hl]
  apply List.ext_getElem
  · simp [ByteCircuit.inputBytes, hH]
  · intro i h1 h2
    simp only [ByteCircuit.inputBytes, List.getElem_map, List.getElem_range]
    rw [BVExpr.eval_var, get_chain _ 0 (1 + i) (Nat.zero_le _), Nat.sub_zero, List.getD_eq_getElem?_getD,
      show 1 + i = i + 1 by omega, List.getElem?_cons_succ, List.getElem?_map,
      List.getElem?_eq_getElem (show i < H.length by simp [ByteCircuit.inputBytes] at h1; omega)]
    simp [pack8]

/-- **`tls-derive` on the bundle `deriveScript` builds**: the client and server handshake traffic
blocks and the main secret of the RFC 8446 schedule on the agreement's bytes and the hello hash. -/
theorem derive_out (aw : Bits) (H : B8) (haw : aw.length = 255) (hH : H.length = 32) :
    shapedOut HybridKernel.tlsDerive (aw ++ bitsOf H) =
      trafficBlockValue (TlsKdf.handshakeSecrets Sha256.concrete (agreementBytes aw) H).client ++
      trafficBlockValue (TlsKdf.handshakeSecrets Sha256.concrete (agreementBytes aw) H).server ++
      (TlsKdf.handshakeSecrets Sha256.concrete (agreementBytes aw) H).main := by
  have hs := TlsMpc.KernelSpecs.TlsHandshake.tlsDerive_spec (chain 0 (⟨BitVec.ofBoolListLE aw⟩ :: H.map pack8))
  dsimp only at hs
  rw [derive_get_agreement, derive_get_hash _ H hH] at hs
  simp only [shapedOut, derive_assign aw H haw hH, hs, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.append_assoc]

theorem trafficBlockValue_length (s : B8) (hs : s.length = 32) : (trafficBlockValue s).length = 60 := by
  unfold trafficBlockValue TlsKdf.trafficKeys TlsKdf.expandLabelCore
  rw [List.length_append, List.length_append, hs, TlsKdf.expandCore_length, TlsKdf.expandCore_length]

theorem client_length (ecdhe h : B8) : (TlsKdf.handshakeSecrets Sha256.concrete ecdhe h).client.length = 32 := by
  simp only [TlsKdf.handshakeSecrets, TlsKdf.deriveSecret, TlsKdf.expandLabelCore, TlsKdf.expandCore_length]

theorem server_length (ecdhe h : B8) : (TlsKdf.handshakeSecrets Sha256.concrete ecdhe h).server.length = 32 := by
  simp only [TlsKdf.handshakeSecrets, TlsKdf.deriveSecret, TlsKdf.expandLabelCore, TlsKdf.expandCore_length]

theorem main_length (ecdhe h : B8) : (TlsKdf.handshakeSecrets Sha256.concrete ecdhe h).main.length = 32 := by
  simp only [TlsKdf.handshakeSecrets, TlsKdf.extract, Sha256.hmac_length]

theorem bools_drop_self (I : Ideal) (h : BoolH) : (I.dropBool h).bools h.id = none := by
  simp [Ideal.dropBool]

theorem localStep_run_eq' (E : Env) (out : BoolH) (name : Bytes) (copies : Nat) (input : BoolH) (I : Ideal)
    (c : Engine.Circuit) (v w : Bits) (hc : E.circuits name = some c) (hv : I.bools input.id = some v)
    (hl : v.length = copies * c.inWidth) (hw : runCopies c copies v = w) :
    localStep E (.run out name copies input) I = some (I.setBool out w) := by
  rw [localStep_run E out name copies input I c v hc hv hl, hw]

theorem derive_inWidth : (shapedCircuit HybridKernel.tlsDerive (List.replicate 1216 .never)).inWidth = 511 := by
  show (HybridKernel.tlsDerive.inputs.map (·.2.bits)).sum = 511
  rw [derive_inputs]
  rfl

/-- **`deriveScript`, two honest parties** (gap F15): with the agreement word `aw` (255 bits, S11's
`Curve.agree`) behind its handle and the public hello hash, the run returns the three handles, which
hold the client handshake traffic block, the server handshake traffic block and the main secret of
`TlsKdf.handshakeSecrets` on `agreementBytes aw` and the hash; the agreement's handle is freed. -/
theorem derive_honest (E : Env)
    (hE : E.circuits deriveName = some (shapedCircuit HybridKernel.tlsDerive (List.replicate 1216 .never)))
    (n : Nat) (agreement : BoolH) (han : agreement.id < n) (aw : Bits) (haw : aw.length = 255) (H : B8)
    (hH : H.length = 32) (σA σB : Store) (I : Ideal) (hIa : I.bools agreement.id = some aw) :
    ∃ J, JRet (jointRun E (deriveScript n agreement H) (deriveScript n agreement H) σA σB I)
        ⟨⟨n + 3⟩, ⟨n + 4⟩, ⟨n + 5⟩⟩ ⟨⟨n + 3⟩, ⟨n + 4⟩, ⟨n + 5⟩⟩ J σA σB ∧
      J.bools (n + 3) = some (bitsOf (trafficBlockValue (TlsKdf.handshakeSecrets Sha256.concrete (agreementBytes aw) H).client)) ∧
      J.bools (n + 4) = some (bitsOf (trafficBlockValue (TlsKdf.handshakeSecrets Sha256.concrete (agreementBytes aw) H).server)) ∧
      J.bools (n + 5) = some (bitsOf (TlsKdf.handshakeSecrets Sha256.concrete (agreementBytes aw) H).main) ∧
      J.bools agreement.id = none := by
  have hD := derive_out aw H haw hH
  generalize hS : TlsKdf.handshakeSecrets Sha256.concrete (agreementBytes aw) H = S at hD ⊢
  have hc : (trafficBlockValue S.client).length = 60 := by
    rw [trafficBlockValue_length _ (by rw [← hS]; exact client_length _ _)]
  have hs : (trafficBlockValue S.server).length = 60 := by
    rw [trafficBlockValue_length _ (by rw [← hS]; exact server_length _ _)]
  have hm : S.main.length = 32 := by rw [← hS]; exact main_length _ _
  have hDl : (shapedOut HybridKernel.tlsDerive (aw ++ bitsOf H)).length = 152 := by
    rw [hD]; simp only [List.length_append, hc, hs, hm]
  have hb : (bitsOf (shapedOut HybridKernel.tlsDerive (aw ++ bitsOf H))).length = 8 * 152 := by rw [length_bitsOf, hDl]
  have hrun : runCopies (shapedCircuit HybridKernel.tlsDerive (List.replicate 1216 .never)) 1 (aw ++ bitsOf H) =
      bitsOf (shapedOut HybridKernel.tlsDerive (aw ++ bitsOf H)) := by
    rw [runCopies_one' _ _ (by rw [derive_inWidth, List.length_append, haw, length_bitsOf, hH])]
    rfl
  have e1 : (shapedOut HybridKernel.tlsDerive (aw ++ bitsOf H)).take 60 = trafficBlockValue S.client := by
    rw [hD, List.append_assoc, List.take_left' hc]
  have e2 : ((shapedOut HybridKernel.tlsDerive (aw ++ bitsOf H)).drop 60).take 60 = trafficBlockValue S.server := by
    rw [hD, List.append_assoc, List.drop_left' hc, List.take_left' hs]
  have e3 : ((shapedOut HybridKernel.tlsDerive (aw ++ bitsOf H)).drop 120).take 32 = S.main := by
    rw [hD, show (120 : Nat) = 60 + 60 from rfl, ← List.drop_drop, List.append_assoc, List.drop_left' hc,
      List.drop_left' hs, List.take_of_length_le (by omega)]
  unfold deriveScript
  simp only [seqs_cons, seqs_nil]
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_public E ⟨n⟩ (bitsOf H) I) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_concat2 E ⟨n + 1⟩ agreement ⟨n⟩ _ aw (bitsOf H)
    (aw ++ bitsOf H) (by ival_tac) (by ival_tac) rfl) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_run_eq' E ⟨n + 2⟩ _ 1 ⟨n + 1⟩ _ _ (aw ++ bitsOf H)
    (bitsOf (shapedOut HybridKernel.tlsDerive (aw ++ bitsOf H))) hE (by ival_tac)
    (by rw [Nat.one_mul, derive_inWidth, List.length_append, haw, length_bitsOf, hH]) hrun) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_slice E ⟨n + 3⟩ ⟨n + 2⟩ 0 480 _
    (bitsOf (shapedOut HybridKernel.tlsDerive (aw ++ bitsOf H)))
    (bitsOf (trafficBlockValue S.client)) (by ival_tac) (by rw [hb]; omega)
    (by rw [slice_bitsOf' _ 0 60 0 480 rfl rfl, List.drop_zero, Nat.sub_zero, e1])) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_slice E ⟨n + 4⟩ ⟨n + 2⟩ 480 960 _
    (bitsOf (shapedOut HybridKernel.tlsDerive (aw ++ bitsOf H)))
    (bitsOf (trafficBlockValue S.server)) (by ival_tac) (by rw [hb]; omega)
    (by rw [slice_bitsOf' _ 60 120 480 960 rfl rfl, show 120 - 60 = 60 from rfl, e2])) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_slice E ⟨n + 5⟩ ⟨n + 2⟩ 960 1216 _
    (bitsOf (shapedOut HybridKernel.tlsDerive (aw ++ bitsOf H)))
    (bitsOf S.main) (by ival_tac) (by rw [hb]; omega)
    (by rw [slice_bitsOf' _ 120 152 960 1216 rfl rfl, show 152 - 120 = 32 from rfl, e3])) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_free E _ _) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_free E _ _) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_free E _ _) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_free E _ _) ?_
  exact ex_done E _ _ σA σB _ _ ⟨by ival_tac, by ival_tac, by ival_tac, bools_drop_self _ _⟩

end TlsMpc.Node.Flows.Tls
