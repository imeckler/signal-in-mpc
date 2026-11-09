import TlsMpc.Signal.PrivateReusableOutboxV1
namespace TlsMpc.Signal.PrivateShardedAccountV1
open PrivateAccountAdmissionV2
-- The global shard is8306B. A conversation shard is12611B: the predecessor
-- layout with eight generation bytes appended to each of its four outbox cells.
def globalValid (a : ByteAuth.Ops B) (raw : List B) : B :=
 if raw.length=8306 then all a [canonicalPayload a 8192 (slice raw 103 8195),
  ByteAuth.eqMask a (OpenResult.get a raw 70) (a.const 5),
  a.maskBit (OpenResult.get a raw 8298) 7,
  a.not (ByteAuth.equalMask a (slice raw 8298 8) (List.replicate 8 (a.const 255)))] else a.const 0
def stripGenerations (queue : List B) : List B :=
 slice queue 0 1302 ++ slice queue 1310 1302 ++ slice queue 2620 1302 ++ slice queue 3930 1302
def legacy (global conversation : List B) : List B :=
 global ++ conversation.take 7367 ++ stripGenerations (slice conversation 7367 5240) ++ slice conversation 12607 4
def conversationValid (s : Sha256.Ops B W) (o : Word64.Ops B V) (a : ByteAuth.Ops B)
 (global conversation : List B) : B :=
 let queue := slice conversation 7367 5240
 let dispositions := slice conversation 12607 4
 if global.length=8306 ∧ conversation.length=12611 then all a
  [OpenResult.get a (PrivateAccountAdmissionV2.validate 1 s o a (legacy global conversation)) 0,
   all a ((List.range 4).map fun i => PrivateReusableOutboxV1.cellValid a (slice queue (i*1310) 1310) (OpenResult.get a dispositions i))]
 else a.const 0
section
variable {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} (ha : ByteAuth.Hom a a' f)
include ha
theorem globalValid_map (raw : List B) : f (globalValid a raw)=globalValid a' (raw.map f) := by
 simp only [globalValid,List.length_map]
 split
 · simp only [all_map ha,List.map_cons,List.map_nil,canonicalPayload_map ha,ByteAuth.eqMask_map ha,
   OpenResult.get_map ha,ha.const,ha.maskBit,ha.not,ByteAuth.equalMask_map ha,slice,List.map_take,List.map_drop,List.map_replicate]
 · exact ha.const 0
theorem legacy_map (global conversation : List B) :
 (legacy global conversation).map f=legacy (global.map f) (conversation.map f) := by
 simp only [legacy,stripGenerations,slice,List.map_append,List.map_take,List.map_drop]
theorem conversationValid_map {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {fw : W → W'}
 (hs : Sha256.Hom s s' f fw) {o : Word64.Ops B V} {o' : Word64.Ops B' V'} {fv : V → V'}
 (ho : Word64.Hom o o' f fv) (global conversation : List B) :
 f (conversationValid s o a global conversation)=conversationValid s' o' a' (global.map f) (conversation.map f) := by
 simp only [conversationValid,List.length_map]
 split
 · simp only [all_map ha,List.map_cons,List.map_nil,OpenResult.get_map ha,
   PrivateAccountAdmissionV2.validate_map ha hs ho,legacy_map ha,PrivateReusableOutboxV1.cellValid_map ha,
   List.map_map,Function.comp_def,slice,List.map_take,List.map_drop]
 · exact ha.const 0
end
open Std.Tactic.BVDecide
theorem compiled_global_correct (input : List (BVExpr 8)) (assignment : BVExpr.Assignment) :
 PrivateProtobuf.CircuitAgreement [globalValid ByteAuth.symbolic input]
  [globalValid ByteAuth.concrete (input.map (BVExpr.eval assignment))] assignment := by
 intro index hi
 rw [ByteCircuit.compile_bytes_correct]
 simp only [List.map_cons,List.map_nil]
 have h := globalValid_map (ByteAuth.evaluationHom assignment) input
 change BVExpr.eval assignment (globalValid ByteAuth.symbolic input) = _ at h
 rw [h]
theorem compiled_conversation_correct (global conversation : List (BVExpr 8)) (assignment : BVExpr.Assignment) :
 PrivateProtobuf.CircuitAgreement [conversationValid Sha256.symbolic Word64.symbolic ByteAuth.symbolic global conversation]
  [conversationValid Sha256.concrete Word64.concrete ByteAuth.concrete (global.map (BVExpr.eval assignment)) (conversation.map (BVExpr.eval assignment))] assignment := by
 intro index hi
 rw [ByteCircuit.compile_bytes_correct]
 simp only [List.map_cons,List.map_nil]
 have h := conversationValid_map (ByteAuth.evaluationHom assignment)
  (Sha256.evaluationHom assignment) (Word64.evaluationHom assignment) global conversation
 change BVExpr.eval assignment (conversationValid Sha256.symbolic Word64.symbolic ByteAuth.symbolic global conversation) = _ at h
 rw [h]
end TlsMpc.Signal.PrivateShardedAccountV1
