import TlsMpc.Signal.CbcOpen
import TlsMpc.Signal.MessageMac

/-! Bounded authenticated Signal opening. MAC content, ciphertext and optional
address bytes are selected from ONE shared serialized input. Public layout
metadata must be established by an in-MPC protobuf parser before general use;
this module does not implement that parser or session-state transitions.
The output is secret status || uint64 length || fixed-size plaintext buffer,
with every output byte zero on MAC, version, address or padding rejection. -/

namespace TlsMpc.Signal.Receive
open Std.Tactic.BVDecide

structure Layout where
  ciphertextOffset : Nat
  ciphertextBytes : Nat
  addressesOffset : Option Nat
  deriving DecidableEq

def Layout.valid (layout : Layout) (wireBytes expectedAddressBytes : Nat) : Prop :=
  9 ≤ wireBytes ∧ 0 < layout.ciphertextBytes ∧ layout.ciphertextBytes % 16 = 0 ∧
  1 ≤ layout.ciphertextOffset ∧ layout.ciphertextOffset + layout.ciphertextBytes ≤ wireBytes - 8 ∧
  match layout.addressesOffset with
  | none => expectedAddressBytes = 0
  | some offset => expectedAddressBytes = 36 ∧ 1 ≤ offset ∧ offset + 36 ≤ wireBytes - 8 ∧
      (offset + 36 ≤ layout.ciphertextOffset ∨ layout.ciphertextOffset + layout.ciphertextBytes ≤ offset)

instance (layout : Layout) (wireBytes expectedAddressBytes : Nat) :
    Decidable (layout.valid wireBytes expectedAddressBytes) := by
  unfold Layout.valid
  cases layout.addressesOffset <;> infer_instance

def ciphertext (layout : Layout) (wire : List B) : List B :=
  ((MessageMac.content wire).drop layout.ciphertextOffset).take layout.ciphertextBytes

/-- libsignal's parser accepts high version nibble 3 or 4; the low nibble is
not checked by that parser. This gate preserves that exact byte-level policy. -/
def versionMask (a : ByteAuth.Ops B) (wire : List B) : B :=
  let high := a.and (OpenResult.get a wire 0) (a.const 240)
  a.xor (ByteAuth.eqMask a high (a.const 48)) (ByteAuth.eqMask a high (a.const 64))

def serviceKindMask (a : ByteAuth.Ops B) (kind : B) : B :=
  a.xor (ByteAuth.eqMask a kind (a.const 0)) (ByteAuth.eqMask a kind (a.const 1))

def deviceMask (a : ByteAuth.Ops B) (device : B) : B :=
  a.and (a.not (ByteAuth.zeroMask a device)) (a.not (a.maskBit device 7))

/-- Expected addresses use fixed-width ServiceId(17) || DeviceId(1), twice.
Validating the kinds/devices avoids accepting byte strings that cannot be
serialized from the corresponding typed addresses. -/
def expectedAddressMask (a : ByteAuth.Ops B) (expected : List B) : B :=
  a.and (serviceKindMask a (OpenResult.get a expected 0))
    (a.and (deviceMask a (OpenResult.get a expected 17))
      (a.and (serviceKindMask a (OpenResult.get a expected 18))
        (deviceMask a (OpenResult.get a expected 35))))

def addressMask (a : ByteAuth.Ops B) (layout : Layout) (wire expected : List B) : B :=
  match layout.addressesOffset with
  | none => a.const 255
  | some offset => a.and (expectedAddressMask a expected)
      (ByteAuth.equalMask a (((MessageMac.content wire).drop offset).take 36) expected)

def authenticatedMask (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (layout : Layout)
    (macKey sender receiver wire expectedAddresses : List B) : B :=
  a.and (MessageMac.verifyMask s a macKey sender receiver wire)
    (a.and (versionMask a wire) (addressMask a layout wire expectedAddresses))

def openCore (o : AesInverse.Ops B) (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (layout : Layout)
    (cipherKey iv macKey sender receiver wire expectedAddresses : List B) : List B :=
  OpenResult.finish a (authenticatedMask s a layout macKey sender receiver wire expectedAddresses)
    (CbcOpen.decryptCore o cipherKey iv (ciphertext layout wire))

def openChecked (o : AesInverse.Ops B) (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (layout : Layout)
    (cipherKey iv macKey sender receiver wire expectedAddresses : List B) : Option (List B) :=
  if cipherKey.length = 32 ∧ iv.length = 16 ∧ macKey.length = 32 ∧ sender.length = 32 ∧
      receiver.length = 32 ∧ wire.length + 130 < 2 ^ 61 ∧ layout.valid wire.length expectedAddresses.length then
    some (openCore o s a layout cipherKey iv macKey sender receiver wire expectedAddresses)
  else none

section Refinement
variable {o : AesInverse.Ops B} {o' : AesInverse.Ops B'}
  {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {fw : W → W'}
  (ho : AesInverse.Hom o o' f) (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)

theorem ciphertext_map (layout : Layout) (wire : List B) :
    (ciphertext layout wire).map f = ciphertext layout (wire.map f) := by
  simp [ciphertext, MessageMac.content]

include ha

theorem versionMask_map (wire : List B) : f (versionMask a wire) = versionMask a' (wire.map f) := by
  simp only [versionMask, ha.xor, ByteAuth.eqMask_map ha, ha.and, ha.const, OpenResult.get_map ha]

theorem serviceKindMask_map (kind : B) : f (serviceKindMask a kind) = serviceKindMask a' (f kind) := by
  simp only [serviceKindMask, ha.xor, ByteAuth.eqMask_map ha, ha.const]

theorem deviceMask_map (device : B) : f (deviceMask a device) = deviceMask a' (f device) := by
  simp only [deviceMask, ha.and, ha.not, ha.maskBit, ByteAuth.zeroMask_map ha]

theorem expectedAddressMask_map (expected : List B) :
    f (expectedAddressMask a expected) = expectedAddressMask a' (expected.map f) := by
  simp only [expectedAddressMask, ha.and, serviceKindMask_map ha, deviceMask_map ha, OpenResult.get_map ha]

theorem addressMask_map (layout : Layout) (wire expected : List B) :
    f (addressMask a layout wire expected) = addressMask a' layout (wire.map f) (expected.map f) := by
  cases he : layout.addressesOffset <;>
    simp [addressMask, he, ha.const, ha.and, expectedAddressMask_map ha, ByteAuth.equalMask_map ha,
      MessageMac.content]

include hs

theorem authenticatedMask_map (layout : Layout) (macKey sender receiver wire expected : List B) :
    f (authenticatedMask s a layout macKey sender receiver wire expected) =
      authenticatedMask s' a' layout (macKey.map f) (sender.map f) (receiver.map f) (wire.map f) (expected.map f) := by
  simp only [authenticatedMask, ha.and, MessageMac.verifyMask_map hs ha, versionMask_map ha, addressMask_map ha]

include ho

theorem openCore_map (layout : Layout) (cipherKey iv macKey sender receiver wire expected : List B) :
    (openCore o s a layout cipherKey iv macKey sender receiver wire expected).map f =
      openCore o' s' a' layout (cipherKey.map f) (iv.map f) (macKey.map f)
        (sender.map f) (receiver.map f) (wire.map f) (expected.map f) := by
  simp only [openCore, OpenResult.finish_map ha, authenticatedMask_map hs ha,
    CbcOpen.decryptCore_map ho, ciphertext_map]

theorem openChecked_map (layout : Layout) (cipherKey iv macKey sender receiver wire expected : List B) :
    (openChecked o s a layout cipherKey iv macKey sender receiver wire expected).map (List.map f) =
      openChecked o' s' a' layout (cipherKey.map f) (iv.map f) (macKey.map f)
        (sender.map f) (receiver.map f) (wire.map f) (expected.map f) := by
  simp only [openChecked, List.length_map]
  split <;> simp_all [openCore_map ho hs ha]

end Refinement

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem versionMask_value (wire : List (BitVec 8)) :
    versionMask ByteAuth.concrete wire =
      if (OpenResult.get ByteAuth.concrete wire 0 &&& 240) = 48 ∨
          (OpenResult.get ByteAuth.concrete wire 0 &&& 240) = 64 then 255 else 0 := by
  have h : ∀ x : BitVec 8,
      ByteAuth.concrete.xor (ByteAuth.eqMask ByteAuth.concrete (x &&& 240) 48)
        (ByteAuth.eqMask ByteAuth.concrete (x &&& 240) 64) =
        if (x &&& 240) = 48 ∨ (x &&& 240) = 64 then 255 else 0 := by decide +kernel
  exact h _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem serviceKindMask_value (kind : BitVec 8) :
    serviceKindMask ByteAuth.concrete kind = if kind = 0 ∨ kind = 1 then 255 else 0 := by
  have h : ∀ x : BitVec 8, serviceKindMask ByteAuth.concrete x =
    if x = 0 ∨ x = 1 then 255 else 0 := by decide +kernel
  exact h kind

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem deviceMask_value (device : BitVec 8) :
    deviceMask ByteAuth.concrete device = if 0 < device.toNat ∧ device.toNat ≤ 127 then 255 else 0 := by
  have h : ∀ x : BitVec 8, deviceMask ByteAuth.concrete x =
    if 0 < x.toNat ∧ x.toNat ≤ 127 then 255 else 0 := by decide +kernel
  exact h device

theorem ciphertext_length (layout : Layout) (wire : List B)
    (hw : 8 ≤ wire.length)
    (hspan : layout.ciphertextOffset + layout.ciphertextBytes ≤ wire.length - 8) :
    (ciphertext layout wire).length = layout.ciphertextBytes := by
  simp only [ciphertext, MessageMac.content, List.length_take, List.length_drop]
  omega

theorem openCore_length (layout : Layout) (cipherKey iv macKey sender receiver wire expected : List B)
    (o : AesInverse.Ops B) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (hv : layout.valid wire.length expected.length) :
    (openCore o s a layout cipherKey iv macKey sender receiver wire expected).length =
      9 + layout.ciphertextBytes := by
  obtain ⟨hw, hn, hc, _, hspan, _⟩ := hv
  have hl := ciphertext_length layout wire (by omega) hspan
  have hd := CbcOpen.decryptCore_length o cipherKey iv (ciphertext layout wire) (by simpa [hl] using hc)
  rw [openCore, OpenResult.finish_length, hd, hl]
  rw [hd, hl]; omega

theorem reject_bad_mac (layout : Layout) (cipherKey iv macKey sender receiver wire expected : List (BitVec 8))
    (hv : layout.valid wire.length expected.length)
    (bad : MessageMac.tag Sha256.concrete macKey sender receiver (MessageMac.content wire) ≠ MessageMac.receivedTag wire) :
    openCore AesInverse.concrete Sha256.concrete ByteAuth.concrete layout
      cipherKey iv macKey sender receiver wire expected = List.replicate (9 + layout.ciphertextBytes) 0 := by
  obtain ⟨hw, hn, hc, _, hspan, _⟩ := hv
  have hl := ciphertext_length layout wire (by omega) hspan
  have hd := CbcOpen.decryptCore_length AesInverse.concrete cipherKey iv
    (ciphertext layout wire) (by simpa [hl] using hc)
  have hz (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  simp only [openCore, authenticatedMask, MessageMac.verifyMask_value, if_neg bad, hz]
  rw [OpenResult.finish_reject_auth _ (by rw [hd, hl]; omega), hd, hl]

theorem reject_bad_version (layout : Layout) (cipherKey iv macKey sender receiver wire expected : List (BitVec 8))
    (hv : layout.valid wire.length expected.length) (bad : versionMask ByteAuth.concrete wire = 0) :
    openCore AesInverse.concrete Sha256.concrete ByteAuth.concrete layout
      cipherKey iv macKey sender receiver wire expected = List.replicate (9 + layout.ciphertextBytes) 0 := by
  obtain ⟨hw, hn, hc, _, hspan, _⟩ := hv
  have hl := ciphertext_length layout wire (by omega) hspan
  have hd := CbcOpen.decryptCore_length AesInverse.concrete cipherKey iv
    (ciphertext layout wire) (by simpa [hl] using hc)
  have hz (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  have hz' (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  simp only [openCore, authenticatedMask, bad, hz, hz']
  rw [OpenResult.finish_reject_auth _ (by rw [hd, hl]; omega), hd, hl]

theorem reject_bad_address (layout : Layout) (cipherKey iv macKey sender receiver wire expected : List (BitVec 8))
    (hv : layout.valid wire.length expected.length) (bad : addressMask ByteAuth.concrete layout wire expected = 0) :
    openCore AesInverse.concrete Sha256.concrete ByteAuth.concrete layout
      cipherKey iv macKey sender receiver wire expected = List.replicate (9 + layout.ciphertextBytes) 0 := by
  obtain ⟨hw, hn, hc, _, hspan, _⟩ := hv
  have hl := ciphertext_length layout wire (by omega) hspan
  have hd := CbcOpen.decryptCore_length AesInverse.concrete cipherKey iv
    (ciphertext layout wire) (by simpa [hl] using hc)
  have hz (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  simp only [openCore, authenticatedMask, bad, hz]
  rw [OpenResult.finish_reject_auth _ (by rw [hd, hl]; omega), hd, hl]

theorem compiled_openCore_correct (layout : Layout)
    (cipherKey iv macKey sender receiver wire expected : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (openCore AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic layout
      cipherKey iv macKey sender receiver wire expected).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (openCore AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic layout
          cipherKey iv macKey sender receiver wire expected))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (openCore AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic layout
          cipherKey iv macKey sender receiver wire expected))).vec.get index hi)) =
      (ByteCircuit.joinValue (openCore AesInverse.concrete Sha256.concrete ByteAuth.concrete layout
        (cipherKey.map (BVExpr.eval assign)) (iv.map (BVExpr.eval assign)) (macKey.map (BVExpr.eval assign))
        (sender.map (BVExpr.eval assign)) (receiver.map (BVExpr.eval assign))
        (wire.map (BVExpr.eval assign)) (expected.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, openCore_map (AesInverse.evaluationHom assign)
    (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]

end TlsMpc.Signal.Receive
