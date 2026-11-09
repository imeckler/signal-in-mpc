import AesCtrBlockWork.FixsliceCircuitV1Work.Cipher64
import AesKeyScheduleWork.FullSchedule
namespace LibSignalReference.Candidate.FixsliceCircuitV1
open TlsMpc TlsMpc.Signal.AesLayout TlsMpc.Signal.AesLinear
open Aeneas Aeneas.Std
open _root_.Std.Tactic.BVDecide
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

def groupAt (zero : W) (words : List W) (round : Nat) : Words W :=
 fromList zero (words.drop (8*round))

theorem groupAt_map (f : W→W') (zero : W) (words : List W) (round : Nat) :
 mapWords f (groupAt zero words round)=groupAt (f zero) (words.map f) round := by
 simp only [groupAt,fromList_map,List.map_drop]

theorem fromList_eight (zero : W) (words : List W) (hlen : words.length=8) :
 (fromList zero words).list=words := by
 apply List.ext_getElem
 · simp [Words.list,hlen]
 · intro i hi hx
   have hi8 : i<8 := by simpa [Words.list] using hi
   interval_cases i <;>simp [fromList,Words.list,hx]

theorem fromList_take (zero : W) (words : List W) :
 fromList zero (words.take 8)=fromList zero words := by
 simp [fromList]

theorem groupAt_list (zero : W) (words : List W) (round : Nat) (hr : 8*round+8≤words.length) :
 (groupAt zero words round).list=(words.drop (8*round)).take 8 := by
 rw [groupAt,←fromList_take]
 apply fromList_eight
 simp only [List.length_take,List.length_drop]
 omega

theorem chunks_take (words : List W) (count : Nat) :
 (List.range count).flatMap (fun r=>(words.drop (8*r)).take 8)=words.take (8*count) := by
 induction count with
 | zero=>simp
 | succ n ih=>
   simp only [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,ih]
   rw [←List.take_add]
   congr 1

theorem flatten_groups (zero : W) (words : List W) (hlen : words.length=120) :
 (List.range 15).flatMap (fun r=>(groupAt zero words r).list)=words := by
 calc
  _=(List.range 15).flatMap (fun r=>(words.drop (8*r)).take 8) := by
    apply List.flatMap_congr
    intro r hr
    apply groupAt_list
    have hr15 : r<15 := by simpa using hr
    omega
  _=words.take (8*15) := chunks_take words 15
  _=words := by rw [show 8*15=120 from by decide,←hlen,List.take_length]

def scheduleValue (key : Nat→BitVec 8) : List (BitVec 64) :=
 TlsMpc.Signal.AesKeySchedule.scheduleCore TlsMpc.Signal.AesKeySchedule.concrete
  (TlsMpc.Signal.AesKeySchedule.initialWords key 0) (TlsMpc.Signal.AesKeySchedule.initialWords key 16)
def scheduleExpression (key : Nat→BVExpr 8) : List (BVExpr 64) :=
 TlsMpc.Signal.AesKeySchedule.scheduleCore TlsMpc.Signal.AesKeySchedule.symbolic
  (TlsMpc.Signal.AesKeySchedule.initialWordsExpr key 0) (TlsMpc.Signal.AesKeySchedule.initialWordsExpr key 16)

attribute [local irreducible] scheduleValue scheduleExpression

theorem scheduleExpression_correct (key : Nat→BVExpr 8) (assign : BVExpr.Assignment) :
 (scheduleExpression key).map (BVExpr.eval assign)=scheduleValue (fun i=>(key i).eval assign) := by
 simp only [scheduleExpression,scheduleValue,TlsMpc.Signal.AesKeySchedule.scheduleCore_map
  (TlsMpc.Signal.AesKeySchedule.evaluationHom assign),TlsMpc.Signal.AesKeySchedule.initialWordsExpr_refines]

def keyGroupsExpression (key : Nat→BVExpr 8) : Nat→Words (BVExpr 64) :=
 groupAt (.const 0) (scheduleExpression key)

theorem keyGroupsExpression_correct (key : Nat→BVExpr 8) (assign : BVExpr.Assignment) (round : Nat) :
 mapWords (BVExpr.eval assign) (keyGroupsExpression key round)=
 groupAt 0 (scheduleValue (fun i=>(key i).eval assign)) round := by
 simp only [keyGroupsExpression,groupAt_map,BVExpr.eval_const,scheduleExpression_correct]

theorem scheduleValue_length (key : Nat→BitVec 8) : (scheduleValue key).length=120 := by
 obtain ⟨result,_,hv⟩:=AesKeySchedule.key_schedule_spec (fun i=>(⟨key i⟩ : U8))
 have hv' : result.val.map UScalar.bv=scheduleValue key := by
  unfold scheduleValue
  exact hv
 have h:=congrArg List.length hv'
 rw [List.length_map,result.property] at h
 simpa using h.symm

theorem keyArray_groups (words : List (BitVec 64)) (hlen : words.length=120) :
 (AesKeyRanges.keyArray (groupAt 0 words)).val.map UScalar.bv=words := by
 with_unfolding_all simpa [AesKeyRanges.keyArray,List.map_flatMap,List.map_map,Function.comp_def]
   using flatten_groups (0 : BitVec 64) words hlen

theorem map_bv_injective (a b : List U64) (h : a.map UScalar.bv=b.map UScalar.bv) : a=b := by
 have restore (xs : List U64) : (xs.map UScalar.bv).map (fun byte : BitVec 64=>(⟨byte⟩ : U64))=xs := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>simp only [List.map_cons,ih]
 have h':=congrArg (List.map (fun byte : BitVec 64=>(⟨byte⟩ : U64))) h
 rw [restore a,restore b] at h'
 exact h'

theorem actual_schedule (key : Nat→BitVec 8) :
 ∃ schedule,
  RustCryptoAesKeySchedule.soft.fixslice.aes256_key_schedule (AesKeySchedule.keyArray (fun i=>(⟨key i⟩ : U8))) = .ok schedule ∧
  schedule=AesKeyRanges.keyArray (groupAt 0 (scheduleValue key)) := by
 obtain ⟨result,hc,hv⟩:=AesKeySchedule.key_schedule_spec (fun i=>(⟨key i⟩ : U8))
 refine ⟨result,hc,?_⟩
 apply Subtype.ext
 apply map_bv_injective
 have hv' : result.val.map UScalar.bv=scheduleValue key := by
  unfold scheduleValue
  exact hv
 exact hv'.trans (keyArray_groups (scheduleValue key) (scheduleValue_length key)).symm
end LibSignalReference.Candidate.FixsliceCircuitV1
