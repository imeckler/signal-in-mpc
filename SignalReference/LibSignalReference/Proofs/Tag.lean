import LibSignalReference.Generated.ServiceIdEncode.Funs
import LibSignalReference.Generated.MessageType.Funs
import TlsMpc.Signal.Tag

/-!
Complete tag-decoder equivalences, including malformed bytes and the original
byte in TryFromReprError. The finite input theorems below quantify over *every*
8-bit input and are checked by Lean's kernel; they are not fixture tests or
native_decide assumptions. The parser's surrounding Result/Option composition
remains a separate extraction obligation.
-/

namespace LibSignalReference.Proofs.Tag

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

open Aeneas Aeneas.Std

abbrev ServiceResult := core.result.Result LibSignalServiceId.address.ServiceIdKind
  (LibSignalServiceId.derive_more.convert.try_from.TryFromReprError U8)

abbrev MessageResult := core.result.Result LibSignalMessageType.protocol.CiphertextMessageType
  (LibSignalMessageType.derive_more.convert.try_from.TryFromReprError U8)

def serviceEncoding : ServiceResult → List (BitVec 8)
  | .Ok .Aci => [1#8, 0#8]
  | .Ok .Pni => [1#8, 1#8]
  | .Err error => [0#8, error.input.bv]

def messageEncoding : MessageResult → List (BitVec 8)
  | .Ok .Whisper => [1#8, 2#8]
  | .Ok .PreKey => [1#8, 3#8]
  | .Ok .SenderKey => [1#8, 7#8]
  | .Ok .Plaintext => [1#8, 8#8]
  | .Err error => [0#8, error.input.bv]

def execution (encode : α → List (BitVec 8)) : Result α → Option (List (BitVec 8))
  | .ok result => some (encode result)
  | .fail _ | .div => none

private theorem service_all : ∀ byte : BitVec 8,
    execution serviceEncoding
      (LibSignalServiceId.address.ServiceIdKind.Insts.CoreConvertTryFromU8TryFromReprErrorU8.try_from
        ⟨byte⟩) = some (TlsMpc.Signal.Tag.value [0, 1] byte) := by
  decide +kernel

private theorem message_all : ∀ byte : BitVec 8,
    execution messageEncoding
      (LibSignalMessageType.protocol.CiphertextMessageType.Insts.CoreConvertTryFromU8TryFromReprErrorU8.try_from
        ⟨byte⟩) = some (TlsMpc.Signal.Tag.value [2, 3, 7, 8] byte) := by
  decide +kernel

theorem service_spec (byte : U8) :
    ∃ result,
      LibSignalServiceId.address.ServiceIdKind.Insts.CoreConvertTryFromU8TryFromReprErrorU8.try_from
        byte = .ok result ∧ serviceEncoding result = TlsMpc.Signal.Tag.value [0, 1] byte.bv := by
  have all := service_all byte.bv
  cases hr : LibSignalServiceId.address.ServiceIdKind.Insts.CoreConvertTryFromU8TryFromReprErrorU8.try_from byte with
  | ok result => exact ⟨result, rfl, by simpa [hr, execution] using all⟩
  | fail error => simp [hr, execution] at all
  | div => simp [hr, execution] at all

theorem message_spec (byte : U8) :
    ∃ result,
      LibSignalMessageType.protocol.CiphertextMessageType.Insts.CoreConvertTryFromU8TryFromReprErrorU8.try_from
        byte = .ok result ∧ messageEncoding result = TlsMpc.Signal.Tag.value [2, 3, 7, 8] byte.bv := by
  have all := message_all byte.bv
  cases hr : LibSignalMessageType.protocol.CiphertextMessageType.Insts.CoreConvertTryFromU8TryFromReprErrorU8.try_from byte with
  | ok result => exact ⟨result, rfl, by simpa [hr, execution] using all⟩
  | fail error => simp [hr, execution] at all
  | div => simp [hr, execution] at all

theorem serviceEncoding_injective : Function.Injective serviceEncoding := by
  intro a b h
  cases a with
  | Ok ak =>
    cases ak <;> cases b with
    | Ok bk => cases bk <;> simp_all [serviceEncoding]
    | Err be => simp_all [serviceEncoding]
  | Err ae =>
    cases b with
    | Ok bk => cases bk <;> simp_all [serviceEncoding]
    | Err be =>
      simp only [serviceEncoding, List.cons.injEq, and_true, true_and] at h
      cases ae
      cases be
      congr 2
      exact (UScalar.eq_equiv_bv_eq _ _).mpr h

theorem messageEncoding_injective : Function.Injective messageEncoding := by
  intro a b h
  cases a with
  | Ok ak =>
    cases ak <;> cases b with
    | Ok bk => cases bk <;> simp_all [messageEncoding]
    | Err be => simp_all [messageEncoding]
  | Err ae =>
    cases b with
    | Ok bk => cases bk <;> simp_all [messageEncoding]
    | Err be =>
      simp only [messageEncoding, List.cons.injEq, and_true, true_and] at h
      cases ae
      cases be
      congr 2
      exact (UScalar.eq_equiv_bv_eq _ _).mpr h

def RefinesArtifact (source : Result α) (encode : α → List (BitVec 8))
    (tags : List Nat) (byte : _root_.Std.Tactic.BVDecide.BVExpr 8)
    (assign : _root_.Std.Tactic.BVDecide.BVExpr.Assignment) : Prop :=
  ∃ result, source = .ok result ∧
    ∀ (index : Nat) (hi : index < 8 * (TlsMpc.Signal.Tag.symbolic tags byte).length),
      TlsMpc.AigExport.evalRef
        (TlsMpc.AigExport.exportNodes (TlsMpc.AigExport.compile
          (TlsMpc.ByteCircuit.joinExpr (TlsMpc.Signal.Tag.symbolic tags byte))).aig)
        (fun varId bit => (assign.get varId).bv.getLsbD bit)
        (TlsMpc.AigExport.exportRef ((TlsMpc.AigExport.compile
          (TlsMpc.ByteCircuit.joinExpr (TlsMpc.Signal.Tag.symbolic tags byte))).vec.get index hi)) =
        (TlsMpc.ByteCircuit.joinValue (encode result)).getLsbD index

private theorem compile_refines (source : Result α) (encode : α → List (BitVec 8))
    (tags : List Nat) (byte : _root_.Std.Tactic.BVDecide.BVExpr 8)
    (assign : _root_.Std.Tactic.BVDecide.BVExpr.Assignment)
    (spec : ∃ result, source = .ok result ∧
      encode result = TlsMpc.Signal.Tag.value tags (byte.eval assign)) :
    RefinesArtifact source encode tags byte assign := by
  obtain ⟨result, hr, hbytes⟩ := spec
  refine ⟨result, hr, ?_⟩
  intro index hi
  rw [TlsMpc.Signal.Tag.compiled_classify_correct, ← hbytes]

theorem service_refines_artifact (byte : _root_.Std.Tactic.BVDecide.BVExpr 8)
    (assign : _root_.Std.Tactic.BVDecide.BVExpr.Assignment) :
    RefinesArtifact
      (LibSignalServiceId.address.ServiceIdKind.Insts.CoreConvertTryFromU8TryFromReprErrorU8.try_from
        ⟨byte.eval assign⟩) serviceEncoding [0, 1] byte assign := by
  exact compile_refines _ _ _ _ _ (service_spec ⟨byte.eval assign⟩)

theorem message_refines_artifact (byte : _root_.Std.Tactic.BVDecide.BVExpr 8)
    (assign : _root_.Std.Tactic.BVDecide.BVExpr.Assignment) :
    RefinesArtifact
      (LibSignalMessageType.protocol.CiphertextMessageType.Insts.CoreConvertTryFromU8TryFromReprErrorU8.try_from
        ⟨byte.eval assign⟩) messageEncoding [2, 3, 7, 8] byte assign := by
  exact compile_refines _ _ _ _ _ (message_spec ⟨byte.eval assign⟩)

end LibSignalReference.Proofs.Tag
