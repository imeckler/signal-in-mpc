import TlsMpc.Signal.PrivateShardedAccountV1
import TlsMpc.Signal.PrivateAccountOutboxV1
namespace TlsMpc.Signal.PrivateShardedOutboxResumeV1
open PrivateAccountAdmissionV2
-- Full shard validation precedes this selector. Expected generation comes from
-- the authorized public certificate ancestry, never from an opened private ID.
def select (a : ByteAuth.Ops B) (ordinal : Nat) (input : List B) : List B :=
 let queue := slice input 1 5240
 let dispositions := slice input 5241 4
 let expected := slice input 5245 8
 let generation := slice queue (ordinal*1310+1302) 8
 let old := PrivateAccountOutboxV1.select a ordinal
  ([OpenResult.get a input 0]++PrivateShardedAccountV1.stripGenerations queue++dispositions)
 let valid := if input.length=5253 ∧ ordinal<4 then all a
  [ByteAuth.eqMask a (OpenResult.get a old 0) (a.const 255),ByteAuth.equalMask a generation expected,
   a.not (ByteAuth.equalMask a expected (List.replicate 8 (a.const 0)))] else a.const 0
 valid :: ByteAuth.release a valid (old.drop 1)
theorem select_map {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'}
 (ha : ByteAuth.Hom a a' f) (ordinal : Nat) (input : List B) :
 (select a ordinal input).map f=select a' ordinal (input.map f) := by
 have strip (queue : List B) : (PrivateShardedAccountV1.stripGenerations queue).map f=
   PrivateShardedAccountV1.stripGenerations (queue.map f) := by
  simp only [PrivateShardedAccountV1.stripGenerations,slice,List.map_append,List.map_drop,List.map_take]
 simp only [select,List.length_map]
 split <;> simp only [List.map_cons,ByteAuth.release_map ha,List.map_drop]
 · simp only [all_map ha,List.map_cons,List.map_nil,ByteAuth.eqMask_map ha,OpenResult.get_map ha,
   PrivateAccountOutboxV1.select_map ha,List.map_append,List.map_cons,List.map_nil,strip,
   ha.const,ByteAuth.equalMask_map ha,ha.not,List.map_replicate,slice,List.map_drop,List.map_take]
 · simp only [ha.const,PrivateAccountOutboxV1.select_map ha,List.map_append,List.map_cons,List.map_nil,
   OpenResult.get_map ha,strip,slice,List.map_drop,List.map_take]
open Std.Tactic.BVDecide
theorem compiled_select_correct (ordinal : Nat) (input : List (BVExpr 8)) (assignment : BVExpr.Assignment) :
 PrivateProtobuf.CircuitAgreement (select ByteAuth.symbolic ordinal input)
  (select ByteAuth.concrete ordinal (input.map (BVExpr.eval assignment))) assignment := by
 intro index hi
 rw [ByteCircuit.compile_bytes_correct,select_map (ByteAuth.evaluationHom assignment)]
end TlsMpc.Signal.PrivateShardedOutboxResumeV1
