import TlsMpc.Signal.PrivateAccountAdmissionV2Proofs
namespace TlsMpc.Signal.PrivateReusableOutboxV1
open PrivateAccountAdmissionV2
-- Cell = old entry1302B || generationBE8. Generation is public certificate
-- metadata represented as shared bytes, never a Signal request identifier.
def cellBytes : Nat := 1310
def queueBytes : Nat := 5240
def eligible (a : ByteAuth.Ops B) (present disposition : B) : B :=
 a.xor (a.and (ByteAuth.eqMask a present (a.const 0)) (ByteAuth.eqMask a disposition (a.const 0)))
  (a.and (ByteAuth.eqMask a present (a.const 255)) (ByteAuth.eqMask a disposition (a.const 3)))
def cellValid (a : ByteAuth.Ops B) (cell : List B) (disposition : B) : B :=
 let absent := all a [ByteAuth.equalMask a cell (List.replicate cellBytes (a.const 0)),ByteAuth.eqMask a disposition (a.const 0)]
 let present := all a [ByteAuth.eqMask a (OpenResult.get a cell 0) (a.const 255),oneOf a disposition [1,2,3,4,5],
  canonicalPayload a 1290 (slice cell 1 1293),a.not (ByteAuth.equalMask a (slice cell 1302 8) (List.replicate 8 (a.const 0)))]
 a.xor absent present
-- Input: upstreamvalid1 || queue5240 || dispositions4 || newcell1310 ||
-- expected public certificate-generationBE8. Output: validity1||queue||disp.
def candidate (ordinal : Nat) (queue dispositions newCell : List B) (a : ByteAuth.Ops B) : List B :=
 queue.take (ordinal*cellBytes) ++ newCell ++ queue.drop ((ordinal+1)*cellBytes) ++
 dispositions.take ordinal ++ [a.const 1] ++ dispositions.drop (ordinal+1)
def validity (a : ByteAuth.Ops B) (ordinal : Nat) (input : List B) : B :=
 let queue := slice input 1 queueBytes
 let dispositions := slice input (1+queueBytes) 4
 let newCell := slice input (1+queueBytes+4) cellBytes
 let generation := slice input (1+queueBytes+4+cellBytes) 8
 let old := slice queue (ordinal*cellBytes) cellBytes
 if ordinal<4 ∧ input.length=6563 then all a
  [ByteAuth.eqMask a (OpenResult.get a input 0) (a.const 255),
   all a ((List.range 4).map fun i => cellValid a (slice queue (i*cellBytes) cellBytes) (OpenResult.get a dispositions i)),
   eligible a (OpenResult.get a old 0) (OpenResult.get a dispositions ordinal),
   cellValid a newCell (a.const 1),
   ByteAuth.equalMask a (slice newCell 1302 8) generation,
   a.not (ByteAuth.equalMask a (slice old 1302 8) generation)] else a.const 0
def replace (a : ByteAuth.Ops B) (ordinal : Nat) (input : List B) : List B :=
 let valid := validity a ordinal input
 valid :: ByteAuth.release a valid (candidate ordinal (slice input 1 queueBytes)
  (slice input (1+queueBytes) 4) (slice input (1+queueBytes+4) cellBytes) a)

theorem eligible_value (present disposition : BitVec 8) :
 eligible ByteAuth.concrete present disposition =
  if (present=0 ∧ disposition=0) ∨ (present=255 ∧ disposition=3) then 255 else 0 := by
 change ((ByteAuth.eqMask ByteAuth.concrete present 0 &&& ByteAuth.eqMask ByteAuth.concrete disposition 0) ^^^
  (ByteAuth.eqMask ByteAuth.concrete present 255 &&& ByteAuth.eqMask ByteAuth.concrete disposition 3)) = _
 simp only [ByteAuth.eqMask_value]
 by_cases hp0 : present=0 <;> by_cases hp255 : present=255 <;>
  by_cases hd0 : disposition=0 <;> by_cases hd3 : disposition=3 <;> simp_all

theorem eligible_preserves_pending (present : BitVec 8) (disposition : BitVec 8)
 (h : disposition=1 ∨ disposition=2 ∨ disposition=4 ∨ disposition=5) :
 eligible ByteAuth.concrete present disposition=0 := by
 rcases h with h|h|h|h <;> subst disposition <;> simp [eligible_value]

-- No entry outside the public selected cell is rewritten, shifted or discarded.
theorem candidate_preserves_rest (ordinal : Nat) (before old suffix dispositions newCell : List B)
 (a : ByteAuth.Ops B) (hp : before.length=ordinal*cellBytes) (ho : old.length=cellBytes) :
 candidate ordinal (before++old++suffix) dispositions newCell a =
 before++newCell++suffix++dispositions.take ordinal++[a.const 1]++dispositions.drop (ordinal+1) := by
 simp only [candidate, List.append_assoc]
 have ht : (before++(old++suffix)).take (ordinal*cellBytes)=before := by
  rw [← hp, List.take_left]
 have hd : (before++(old++suffix)).drop ((ordinal+1)*cellBytes)=suffix := by
  have he : (ordinal+1)*cellBytes=before.length+old.length := by simp only [Nat.add_mul, Nat.one_mul]; omega
  rw [he, List.drop_append, Nat.add_sub_cancel_left, List.drop_append, Nat.sub_self]
  simp
 rw [ht, hd]

section
variable {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} (ha : ByteAuth.Hom a a' f)
include ha
theorem eligible_map (present disposition : B) :
 f (eligible a present disposition)=eligible a' (f present) (f disposition) := by
 simp only [eligible,ha.xor,ha.and,ByteAuth.eqMask_map ha,ha.const]
theorem cellValid_map (cell : List B) (disposition : B) :
 f (cellValid a cell disposition)=cellValid a' (cell.map f) (f disposition) := by
 simp only [cellValid,ha.xor,all_map ha,List.map_cons,List.map_nil,ByteAuth.equalMask_map ha,
  List.map_replicate,ha.const,ByteAuth.eqMask_map ha,OpenResult.get_map ha,oneOf_map ha,
  canonicalPayload_map ha,ha.not,slice,List.map_take,List.map_drop]
theorem candidate_map (ordinal : Nat) (queue dispositions newCell : List B) :
 (candidate ordinal queue dispositions newCell a).map f=candidate ordinal (queue.map f) (dispositions.map f) (newCell.map f) a' := by
 simp only [candidate,List.map_append,List.map_take,List.map_drop,List.map_cons,List.map_nil,ha.const]
theorem validity_map (ordinal : Nat) (input : List B) :
 f (validity a ordinal input)=validity a' ordinal (input.map f) := by
 simp only [validity,List.length_map]
 split
 · simp only [all_map ha,List.map_cons,List.map_nil,List.map_map,Function.comp_def,
    ByteAuth.eqMask_map ha,OpenResult.get_map ha,ha.const,cellValid_map ha,eligible_map ha,
    ByteAuth.equalMask_map ha,ha.not,slice,List.map_take,List.map_drop]
 · exact ha.const 0
theorem replace_map (ordinal : Nat) (input : List B) :
 (replace a ordinal input).map f=replace a' ordinal (input.map f) := by
 simp only [replace,List.map_cons,ByteAuth.release_map ha,validity_map ha,candidate_map ha,
  slice,List.map_take,List.map_drop]

end
open Std.Tactic.BVDecide
theorem compiled_replace_correct (ordinal : Nat) (input : List (BVExpr 8)) (assignment : BVExpr.Assignment) :
 PrivateProtobuf.CircuitAgreement (replace ByteAuth.symbolic ordinal input)
  (replace ByteAuth.concrete ordinal (input.map (BVExpr.eval assignment))) assignment := by
 intro index hi
 rw [ByteCircuit.compile_bytes_correct,replace_map (ByteAuth.evaluationHom assignment)]
end TlsMpc.Signal.PrivateReusableOutboxV1
