import TlsMpc.Signal.PrivateRecordAdmissionV1
import TlsMpc.Signal.PrivateRecordBindingV1Proofs
namespace TlsMpc.Signal.PrivateRecordAdmissionV1
open PrivateRecordEncodingV1
section
variable {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} (ha : ByteAuth.Hom a a' f)
include ha
 theorem schema_map : (PrivateRecordSchemaV1.schema a).map (Node.map f)=PrivateRecordSchemaV1.schema a' := by
  simp only [PrivateRecordSchemaV1.schema,Node.map,List.map_cons,List.map_nil,
    ha.const,List.map_replicate,PrivateBuffer.zero_map ha]
 theorem validate_map {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {fw : W → W'}
    (hs : Sha256.Hom s s' f fw)
    {o : Word64.Ops B V} {o' : Word64.Ops B' V'} {fv : V → V'}
    (ho : Word64.Hom o o' f fv) (raw : List B) :
    (validate s o a raw).map f=validate s' o' a' (raw.map f) := by
  have hr := congrArg Prod.fst (PrivateRecordSnapshotV1.restore_map ha 16
    (PrivateRecordSchemaV1.schema a) (raw.take 5550))
  simp only [Prod.fst,schema_map ha,List.map_take] at hr
  simp only [validate,List.length_map]
  split <;> simp only [List.map_cons,List.map_nil,ha.const,PrivateRecordBindingV1.all_map ha,
    List.map_cons,List.map_nil,ByteAuth.equalMask_map ha,
    PrivateRecordBindingV1.coherence_map ha hs ho,
    PrivateRecordSnapshotV1.project_map ha ho,PrivateRecordSnapshotV1.flatten_map ha,
    List.map_take,List.map_drop,hr]
end
open Std.Tactic.BVDecide
 theorem compiled_validate_correct (raw : List (BVExpr 8)) (assign : BVExpr.Assignment) :
    PrivateProtobuf.CircuitAgreement (validate Sha256.symbolic Word64.symbolic ByteAuth.symbolic raw)
      (validate Sha256.concrete Word64.concrete ByteAuth.concrete (raw.map (BVExpr.eval assign))) assign := by
  intro index hi
  rw [ByteCircuit.compile_bytes_correct,validate_map (ByteAuth.evaluationHom assign)
    (Sha256.evaluationHom assign) (Word64.evaluationHom assign)]
end TlsMpc.Signal.PrivateRecordAdmissionV1
