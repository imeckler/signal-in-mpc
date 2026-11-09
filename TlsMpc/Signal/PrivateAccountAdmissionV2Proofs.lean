import TlsMpc.Signal.PrivateAccountAdmissionV2
import TlsMpc.Signal.PrivateRecordAdmissionV1Proofs
namespace TlsMpc.Signal.PrivateAccountAdmissionV2
section
variable {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} (ha : ByteAuth.Hom a a' f)
include ha
 theorem all_map (values : List B) : f (all a values)=all a' (values.map f) := by
  unfold all
  exact PrivateRecordOperationsV1Proofs.fold_map f f a.and a'.and ha.and values (a.const 255) |>.trans (by rw [ha.const])
 theorem oneOf_map (value : B) (allowed : List Nat) : f (oneOf a value allowed)=oneOf a' (f value) allowed := by
  unfold oneOf
  rw [← ha.const 0]
  exact (PrivateRecordOperationsV1Proofs.fold_map f id (fun old n => a.xor old (ByteAuth.eqMask a value (a.const n))) (fun old n => a'.xor old (ByteAuth.eqMask a' (f value) (a'.const n))) (by intro old n;simp only [ha.xor,ByteAuth.eqMask_map ha,ha.const,id_eq]) allowed (a.const 0)).trans (by simp only [List.map_id])
 theorem canonicalPayload_map (capacity : Nat) (raw : List B) :
    f (canonicalPayload a capacity raw)=canonicalPayload a' capacity (raw.map f) := by
  have hv := congrArg PrivateBuffer.Buffer.valid (PrivateBuffer.fromWire_map ha capacity raw)
  simp only [PrivateBuffer.Buffer.map] at hv
  simp only [canonicalPayload,ha.and,ByteAuth.eqMask_map ha,ByteAuth.equalMask_map ha,
    PrivateBuffer.output_map ha,PrivateBuffer.fromWire_map ha,ha.const,hv]
 theorem validate_map {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {fw : W → W'}
    (hs : Sha256.Hom s s' f fw) {o : Word64.Ops B V} {o' : Word64.Ops B' V'} {fv : V → V'}
    (ho : Word64.Hom o o' f fv) (n : Nat) (raw : List B) :
    (validate n s o a raw).map f=validate n s' o' a' (raw.map f) := by
  simp only [validate,List.length_map]
  split <;> simp only [List.map_cons,List.map_nil,ha.const]
  simp only [all_map ha,List.map_cons,List.map_nil,List.map_map,Function.comp_def,
    canonicalPayload_map ha,oneOf_map ha,PrivateRecordAdmissionV1.validate_map ha hs ho,
    OpenResult.get_map ha,ByteAuth.equalMask_map ha,ByteAuth.eqMask_map ha,
    ha.and,ha.xor,ha.not,ha.maskBit,ha.const,slice,List.map_take,List.map_drop,
    List.map_append,List.map_replicate]

end
open Std.Tactic.BVDecide
 theorem compiled_validate_correct (n : Nat) (raw : List (BVExpr 8)) (assign : BVExpr.Assignment) :
    PrivateProtobuf.CircuitAgreement (validate n Sha256.symbolic Word64.symbolic ByteAuth.symbolic raw)
      (validate n Sha256.concrete Word64.concrete ByteAuth.concrete (raw.map (BVExpr.eval assign))) assign := by
  intro index hi
  rw [ByteCircuit.compile_bytes_correct,validate_map (ByteAuth.evaluationHom assign)
    (Sha256.evaluationHom assign) (Word64.evaluationHom assign)]
end TlsMpc.Signal.PrivateAccountAdmissionV2
