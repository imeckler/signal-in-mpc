import LibSignalReference.Generated.ServiceIdEncode.Funs
import TlsMpc.Signal.ServiceId

namespace LibSignalReference.Proofs.ServiceId

open Aeneas Aeneas.Std
open LibSignalServiceId

def uuid (self : address.ServiceId) : Array U8 16#usize :=
  match self with
  | .Aci raw | .Pni raw => raw

def kind (self : address.ServiceId) : BitVec 1 :=
  match self with
  | .Aci _ => 0#1
  | .Pni _ => 1#1

def encoded (self : address.ServiceId) : Array U8 17#usize :=
  ⟨⟨0#7 ++ kind self⟩ :: (uuid self).val, by simp⟩

theorem encode_spec (self : address.ServiceId) :
    address.ServiceId.service_id_fixed_width_binary self
      ⦃ result => result = encoded self ⦄ := by
  match self with
  | .Aci raw | .Pni raw =>
    simp only [address.ServiceId.service_id_fixed_width_binary,
      address.ServiceId.kind, address.ServiceId.raw_uuid,
      core.convert.IntoFrom.into,
      U8.Insts.CoreConvertFromServiceIdKind.from,
      uuid.Uuid.Insts.CoreConvertFromSpecificServiceId.from,
      uuid.Uuid.as_bytes]
    step*
    apply Subtype.ext
    simp_all [encoded, kind, uuid, Array.repeat, List.setSlice!]
    rfl

theorem encode_refines_artifact (self : address.ServiceId)
    (secretKind : _root_.Std.Tactic.BVDecide.BVExpr 1)
    (secretUuid : List (_root_.Std.Tactic.BVDecide.BVExpr 8))
    (assign : _root_.Std.Tactic.BVDecide.BVExpr.Assignment)
    (hkind : secretKind.eval assign = kind self)
    (huuid : secretUuid.map (_root_.Std.Tactic.BVDecide.BVExpr.eval assign) =
      (uuid self).val.map (fun byte => byte.bv)) :
    ∃ result, address.ServiceId.service_id_fixed_width_binary self = .ok result ∧
      ∀ (index : Nat)
        (hi : index < 8 * (TlsMpc.Signal.ServiceId.symbolic secretKind secretUuid).length),
        TlsMpc.AigExport.evalRef
          (TlsMpc.AigExport.exportNodes (TlsMpc.AigExport.compile
            (TlsMpc.ByteCircuit.joinExpr
              (TlsMpc.Signal.ServiceId.symbolic secretKind secretUuid))).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (TlsMpc.AigExport.exportRef ((TlsMpc.AigExport.compile
            (TlsMpc.ByteCircuit.joinExpr
              (TlsMpc.Signal.ServiceId.symbolic secretKind secretUuid))).vec.get index hi)) =
          (TlsMpc.ByteCircuit.joinValue (result.val.map (fun byte => byte.bv))).getLsbD index := by
  obtain ⟨result, hr, hresult⟩ := WP.spec_imp_exists (encode_spec self)
  refine ⟨result, hr, ?_⟩
  intro index hi
  rw [TlsMpc.Signal.ServiceId.compiled_encode_correct, hkind, huuid, hresult]
  rfl

end LibSignalReference.Proofs.ServiceId
