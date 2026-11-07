import TlsMpc.Signal.Receive

/-! Direct acceptance/rejection semantics for the bounded receive operation.
This proof connects the secret-mask implementation to ordinary branching on
MAC, supported version and the optional address policy. It adds no parser or
RustCrypto wrapper-refinement claim. -/

namespace TlsMpc.Signal.Receive
open Std.Tactic.BVDecide

def validVersion (wire : List (BitVec 8)) : Prop :=
  (OpenResult.get ByteAuth.concrete wire 0 &&& 240) = 48 ∨
  (OpenResult.get ByteAuth.concrete wire 0 &&& 240) = 64

def validExpectedAddresses (expected : List (BitVec 8)) : Prop :=
  (OpenResult.get ByteAuth.concrete expected 0 = 0 ∨ OpenResult.get ByteAuth.concrete expected 0 = 1) ∧
  (0 < (OpenResult.get ByteAuth.concrete expected 17).toNat ∧ (OpenResult.get ByteAuth.concrete expected 17).toNat ≤ 127) ∧
  (OpenResult.get ByteAuth.concrete expected 18 = 0 ∨ OpenResult.get ByteAuth.concrete expected 18 = 1) ∧
  (0 < (OpenResult.get ByteAuth.concrete expected 35).toNat ∧ (OpenResult.get ByteAuth.concrete expected 35).toNat ≤ 127)

def validAddresses (layout : Layout) (wire expected : List (BitVec 8)) : Prop :=
  match layout.addressesOffset with
  | none => True
  | some offset => validExpectedAddresses expected ∧
      ((MessageMac.content wire).drop offset).take 36 = expected

def authenticated (layout : Layout) (macKey sender receiver wire expected : List (BitVec 8)) : Prop :=
  MessageMac.tag Sha256.concrete macKey sender receiver (MessageMac.content wire) = MessageMac.receivedTag wire ∧
  validVersion wire ∧ validAddresses layout wire expected

instance (wire : List (BitVec 8)) : Decidable (validVersion wire) :=
  inferInstanceAs (Decidable (_ ∨ _))
instance (expected : List (BitVec 8)) : Decidable (validExpectedAddresses expected) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
instance (layout : Layout) (wire expected : List (BitVec 8)) : Decidable (validAddresses layout wire expected) := by
  unfold validAddresses
  cases layout.addressesOffset <;> infer_instance
instance (layout : Layout) (macKey sender receiver wire expected : List (BitVec 8)) :
    Decidable (authenticated layout macKey sender receiver wire expected) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem mask_and (p q : Prop) [Decidable p] [Decidable q] :
    ByteAuth.concrete.and (if p then 255 else 0) (if q then 255 else 0) =
      if p ∧ q then 255 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq, ByteAuth.concrete]

theorem expectedAddressMask_value (expected : List (BitVec 8)) :
    expectedAddressMask ByteAuth.concrete expected = if validExpectedAddresses expected then 255 else 0 := by
  simp only [expectedAddressMask, serviceKindMask_value, deviceMask_value, mask_and,
    validExpectedAddresses]
  split <;> simp_all

theorem addressMask_value (layout : Layout) (wire expected : List (BitVec 8)) :
    addressMask ByteAuth.concrete layout wire expected = if validAddresses layout wire expected then 255 else 0 := by
  cases he : layout.addressesOffset <;>
    simp only [addressMask, he, validAddresses, expectedAddressMask_value,
      ByteAuth.equalMask_value, mask_and, if_true]
  rfl

theorem authenticatedMask_value (layout : Layout) (macKey sender receiver wire expected : List (BitVec 8)) :
    authenticatedMask Sha256.concrete ByteAuth.concrete layout macKey sender receiver wire expected =
      if authenticated layout macKey sender receiver wire expected then 255 else 0 := by
  simp only [authenticatedMask, MessageMac.verifyMask_value, versionMask_value, addressMask_value,
    mask_and, authenticated, validVersion]
  split <;> simp_all

def spec (layout : Layout) (cipherKey iv macKey sender receiver wire expected : List (BitVec 8)) : List (BitVec 8) :=
  if authenticated layout macKey sender receiver wire expected then
    CbcOpen.openCore AesInverse.concrete ByteAuth.concrete cipherKey iv (ciphertext layout wire)
  else List.replicate (9 + layout.ciphertextBytes) 0

theorem openCore_concrete_correct (layout : Layout)
    (cipherKey iv macKey sender receiver wire expected : List (BitVec 8))
    (hv : layout.valid wire.length expected.length) :
    openCore AesInverse.concrete Sha256.concrete ByteAuth.concrete layout
      cipherKey iv macKey sender receiver wire expected =
      spec layout cipherKey iv macKey sender receiver wire expected := by
  obtain ⟨hw, hn, hc, _, hspan, _⟩ := hv
  have hl := ciphertext_length layout wire (by omega) hspan
  have hd := CbcOpen.decryptCore_length AesInverse.concrete cipherKey iv
    (ciphertext layout wire) (by simpa [hl] using hc)
  simp only [openCore, authenticatedMask_value, spec]
  split
  · rfl
  · rw [OpenResult.finish_reject_auth _ (by rw [hd, hl]; omega), hd, hl]

theorem compiled_openCore_spec (layout : Layout)
    (cipherKey iv macKey sender receiver wire expected : List (BVExpr 8))
    (hv : layout.valid wire.length expected.length)
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
      (ByteCircuit.joinValue (spec layout (cipherKey.map (BVExpr.eval assign))
        (iv.map (BVExpr.eval assign)) (macKey.map (BVExpr.eval assign)) (sender.map (BVExpr.eval assign))
        (receiver.map (BVExpr.eval assign)) (wire.map (BVExpr.eval assign)) (expected.map (BVExpr.eval assign)))).getLsbD index := by
  rw [compiled_openCore_correct, openCore_concrete_correct _ _ _ _ _ _ _ _ (by simpa using hv)]

end TlsMpc.Signal.Receive
