import TlsMpc.Signal.PrivateShardedOutboxResumeV1
namespace TlsMpc.Signal.PrivateShardedOutboxRouteV1
open PrivateAccountAdmissionV2
def any (a : ByteAuth.Ops B) (xs : List B) := a.not (all a (xs.map a.not))
def either (a : ByteAuth.Ops B) (x y : B) := a.xor x (a.and (a.not x) y)
def unique (a : ByteAuth.Ops B) (masks : List B) := all a ((List.range 4).map fun i =>
 either a (a.not (OpenResult.get a masks i)) (all a ((List.range 4).map fun j =>
  if j=i then a.const 255 else a.not (OpenResult.get a masks j))))
-- Output: validity1 || pending1 || blocked1 || typedPayload1293 || ID8.
-- Idle/blocked data is zero and MUST NOT be treated as a valid empty send.
def route (a : ByteAuth.Ops B) (ordinal : Nat) (input : List B) : List B :=
 let queue := slice input 1 5240
 let dispositions := slice input 5241 4
 let expected := slice input 5245 8
 let resumable := (List.range 4).map fun i => PrivateAccountOutboxV1.resumable a
  (OpenResult.get a queue (i*1310)) (OpenResult.get a dispositions i)
 let some := any a resumable
 let blocked := any a ((List.range 4).map fun i => all a
  [ByteAuth.eqMask a (OpenResult.get a queue (i*1310)) (a.const 255),ByteAuth.eqMask a (OpenResult.get a dispositions i) (a.const 4)])
 let old := PrivateShardedOutboxResumeV1.select a ordinal input
 let valid := if input.length=5253 ∧ ordinal<4 then all a
  [ByteAuth.eqMask a (OpenResult.get a input 0) (a.const 255),
   all a ((List.range 4).map fun i => PrivateReusableOutboxV1.cellValid a (slice queue (i*1310) 1310) (OpenResult.get a dispositions i)),
   unique a resumable,either a (a.not some) (ByteAuth.eqMask a (OpenResult.get a old 0) (a.const 255)),
   either a (all a [ByteAuth.equalMask a expected (List.replicate 8 (a.const 0)),
     ByteAuth.equalMask a (queue++dispositions) (List.replicate 5244 (a.const 0))])
    (all a [a.not (ByteAuth.equalMask a expected (List.replicate 8 (a.const 0))),
      ByteAuth.eqMask a (OpenResult.get a queue (ordinal*1310)) (a.const 255),
      ByteAuth.equalMask a (slice queue (ordinal*1310+1302) 8) expected])] else a.const 0
 let pending := all a [valid,some,a.not blocked]
 valid::pending::a.and valid blocked::ByteAuth.release a pending (old.drop 1)
section
variable {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} (ha : ByteAuth.Hom a a' f)
include ha
theorem any_map (xs : List B) : f (any a xs)=any a' (xs.map f) := by
 simp only [any,ha.not,all_map ha,List.map_map,Function.comp_def]
theorem either_map (x y : B) : f (either a x y)=either a' (f x) (f y) := by simp only [either,ha.xor,ha.and,ha.not]
theorem unique_map (xs : List B) : f (unique a xs)=unique a' (xs.map f) := by
 simp only [unique,all_map ha,List.map_map,Function.comp_def,either_map ha,ha.not,OpenResult.get_map ha,apply_ite,ha.const]
theorem route_map (ordinal : Nat) (input : List B) :
 (route a ordinal input).map f=route a' ordinal (input.map f) := by
 simp only [route,List.length_map]
 split <;> simp only [List.map_cons,ByteAuth.release_map ha,all_map ha,List.map_cons,List.map_nil,
  List.map_map,Function.comp_def,ha.and,ha.const,ha.not,any_map ha,either_map ha,unique_map ha,
  PrivateAccountOutboxV1.resumable_map ha,PrivateShardedOutboxResumeV1.select_map ha,
  PrivateReusableOutboxV1.cellValid_map ha,OpenResult.get_map ha,ByteAuth.eqMask_map ha,ByteAuth.equalMask_map ha,
  List.map_append,List.map_replicate,slice,List.map_drop,List.map_take]
end
open Std.Tactic.BVDecide
theorem compiled_route_correct (ordinal : Nat) (input : List (BVExpr 8)) (assignment : BVExpr.Assignment) :
 PrivateProtobuf.CircuitAgreement (route ByteAuth.symbolic ordinal input)
  (route ByteAuth.concrete ordinal (input.map (BVExpr.eval assignment))) assignment := by
 intro index hi
 rw [ByteCircuit.compile_bytes_correct,route_map (ByteAuth.evaluationHom assignment)]
end TlsMpc.Signal.PrivateShardedOutboxRouteV1
