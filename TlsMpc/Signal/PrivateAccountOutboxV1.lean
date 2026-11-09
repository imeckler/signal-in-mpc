import TlsMpc.Signal.PrivateAccountAdmissionV2Proofs
namespace TlsMpc.Signal.PrivateAccountOutboxV1
open PrivateAccountAdmissionV2
def resumable (a : ByteAuth.Ops B) (present disposition : B) : B :=
 a.and (ByteAuth.eqMask a present (a.const 255)) (oneOf a disposition [1,2,5])
def select (a : ByteAuth.Ops B) (ordinal : Nat) (input : List B) : List B :=
 let queue := (input.drop 1).take 5208
 let dispositions := (input.drop 5209).take 4
 let entry := slice queue (ordinal*1302) 1302
 let others := (List.range 4).map fun index => if index=ordinal then a.const 255 else
  a.not (resumable a (OpenResult.get a queue (index*1302)) (OpenResult.get a dispositions index))
 let valid := if ordinal<4 ∧ input.length=5213 then all a
  [ByteAuth.eqMask a (OpenResult.get a input 0) (a.const 255),
   resumable a (OpenResult.get a entry 0) (OpenResult.get a dispositions ordinal),all a others,
   canonicalPayload a 1290 (slice entry 1 1293)] else a.const 0
 valid :: ((entry.drop 1).map fun byte => a.and valid byte)

theorem resumable_map {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'}
 (ha : ByteAuth.Hom a a' f) (present disposition : B) :
 f (resumable a present disposition)=resumable a' (f present) (f disposition) := by
 simp only [resumable,ha.and,ByteAuth.eqMask_map ha,ha.const,oneOf_map ha]
theorem select_map {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'}
 (ha : ByteAuth.Hom a a' f) (ordinal : Nat) (input : List B) :
 (select a ordinal input).map f=select a' ordinal (input.map f) := by
 simp only [select,List.length_map]
 split <;> simp only [List.map_cons,List.map_map,Function.comp_def,ha.and,ha.const]
 · simp only [all_map ha,List.map_cons,List.map_nil,ByteAuth.eqMask_map ha,OpenResult.get_map ha,ha.const,
    resumable_map ha,List.map_map,Function.comp_def,List.map_take,List.map_drop,canonicalPayload_map ha,slice,apply_ite,ha.not]
 · simp only [List.map_drop,List.map_take,slice,List.map_map,Function.comp_def]

open Std.Tactic.BVDecide
theorem compiled_select_correct (ordinal : Nat) (input : List (BVExpr 8)) (assignment : BVExpr.Assignment) :
 PrivateProtobuf.CircuitAgreement (select ByteAuth.symbolic ordinal input)
  (select ByteAuth.concrete ordinal (input.map (BVExpr.eval assignment))) assignment := by
 intro index hi
 rw [ByteCircuit.compile_bytes_correct,select_map (ByteAuth.evaluationHom assignment)]
end TlsMpc.Signal.PrivateAccountOutboxV1
