import ProtoParseWork.PrivateLengthV1Work.Plan
import ProtoParseWork.FullParserV3Work.KeyCircuit
namespace PrivateLengthV1.Stack
open TlsMpc TlsMpc.Signal
open LibSignalReference.Candidate.ProstSkipKey

def pad (state : ProtoParse.State (BitVec 8) (BitVec 64)) (count : Nat) :
    ProtoParse.State (BitVec 8) (BitVec 64) :=
  {state with stack := state.stack++List.replicate count 0}

theorem lookup_zeros (index : BitVec 64) (start count : Nat) :
    ProtoParse.lookupWord Word64.concrete ByteAuth.concrete index start (List.replicate count 0) = 0 := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    simp only [List.replicate_succ,ProtoParse.lookupWord,ih]
    simp [Word64.concrete]

theorem lookup_append_zeros (stack : List (BitVec 64)) (index : BitVec 64) (start count : Nat) :
    ProtoParse.lookupWord Word64.concrete ByteAuth.concrete index start (stack++List.replicate count 0) =
    ProtoParse.lookupWord Word64.concrete ByteAuth.concrete index start stack := by
  induction stack generalizing start with
  | nil => exact lookup_zeros _ _ _
  | cons old rest ih => simp only [List.cons_append,ProtoParse.lookupWord,ih]

theorem plan_pad (ending : Nat) (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (count : Nat) :
    ProtoParse.plan Word64.concrete ByteAuth.concrete ending key payload (pad state count) =
    ProtoParse.plan Word64.concrete ByteAuth.concrete ending key payload state := by
  simp only [ProtoParse.plan,pad,lookup_append_zeros]

theorem cursor_pad (ending position : Nat) (lastClear : BitVec 8)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (count : Nat) :
    ProtoParse.planWithCursor Word64.concrete ByteAuth.concrete ending position lastClear key payload (pad state count) =
    ProtoParse.planWithCursor Word64.concrete ByteAuth.concrete ending position lastClear key payload state := by
  unfold ProtoParse.planWithCursor
  rw [plan_pad]
  rfl


theorem write_mask_inside (ending index : Nat) (capacity : ending ≤ 512) (inside : index < ending)
    (enabled : BitVec 8) (depth : BitVec 64) :
    ByteAuth.concrete.and
      (ByteAuth.concrete.and enabled (ByteAuth.concrete.not
        (Word64.concrete.ule (BitVec.ofNat 64 ending) depth)))
      (Word64.eq Word64.concrete ByteAuth.concrete depth (Word64.concrete.const index)) =
    ByteAuth.concrete.and enabled
      (Word64.eq Word64.concrete ByteAuth.concrete depth (Word64.concrete.const index)) := by
  rw [word_eq_value]
  by_cases same : depth = Word64.concrete.const index
  · subst depth
    have guard : Word64.concrete.ule (BitVec.ofNat 64 ending) (Word64.concrete.const index) = 0 := by
      change Word64.concrete.ule (BitVec.ofNat 64 ending) (BitVec.ofNat 64 index) = 0
      rw [Plan.nat_ule _ _ (by omega) (by omega)]
      simp [show ¬ending ≤ index by omega]
    rw [guard]
    simp [ByteAuth.concrete,BitVec.and_assoc]
  · simp [same,ByteAuth.concrete]

theorem write_mask_outside (ending index : Nat) (capacity : index ≤ 512) (outside : ending ≤ index)
    (enabled : BitVec 8) (depth : BitVec 64) :
    ByteAuth.concrete.and
      (ByteAuth.concrete.and enabled (ByteAuth.concrete.not
        (Word64.concrete.ule (BitVec.ofNat 64 ending) depth)))
      (Word64.eq Word64.concrete ByteAuth.concrete depth (Word64.concrete.const index)) = 0 := by
  rw [word_eq_value]
  by_cases same : depth = Word64.concrete.const index
  · subst depth
    have guard : Word64.concrete.ule (BitVec.ofNat 64 ending) (Word64.concrete.const index) = 255 := by
      change Word64.concrete.ule (BitVec.ofNat 64 ending) (BitVec.ofNat 64 index) = 255
      rw [Plan.nat_ule _ _ (by omega) (by omega)]
      simp [outside]
    rw [guard]
    simp [ByteAuth.concrete,BitVec.and_assoc]
  · simp [same,ByteAuth.concrete]

/-- Private unaddressable stack cells remain zero. All actual stack entries
match the accepted parser even for arbitrary current depth/tag/error states. -/
theorem write_stack_pad (stack : List (BitVec 64)) (count ending : Nat)
    (shape : stack.length = min 100 ending) (size : stack.length+count ≤ 100)
    (capacity : ending ≤ 512) (enabled : BitVec 8) (depth tag : BitVec 64) :
    ProtoParse.writeStack Word64.concrete ByteAuth.concrete
      (ByteAuth.concrete.and enabled (ByteAuth.concrete.not
        (Word64.concrete.ule (BitVec.ofNat 64 ending) depth))) depth tag
      (stack++List.replicate count 0) =
    ProtoParse.writeStack Word64.concrete ByteAuth.concrete enabled depth tag stack ++ List.replicate count 0 := by
  apply List.ext_getElem
  · simp [ProtoParse.writeStack]
  · intro index left right
    have bound : index < stack.length+count := by simpa [ProtoParse.writeStack] using left
    by_cases before : index < stack.length
    · simp only [ProtoParse.writeStack,List.getElem_map,List.getElem_zipIdx,Nat.zero_add]
      rw [write_mask_inside ending index capacity (by omega)]
      simp [ProtoParse.writeStack,List.getElem_append_left,before]
    · have outside : ending ≤ index := by omega
      simp only [ProtoParse.writeStack,List.getElem_map,List.getElem_zipIdx,Nat.zero_add]
      rw [write_mask_outside ending index (by omega) outside,Word64.select_reject]
      simp [List.getElem_append,before]



theorem apply_pad (ending position count : Nat) (capacity : ending ≤ 512)
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (shape : state.stack.length = min 100 ending) (size : state.stack.length+count ≤ 100)
    (p : ProtoParse.Plan (BitVec 8) (BitVec 64)) :
    PrivateProtoParseV1.applyPlan Word64.concrete ByteAuth.concrete (BitVec.ofNat 64 ending)
      position p (pad state count) =
    pad (ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state) count := by
  dsimp only [PrivateProtoParseV1.applyPlan,ProtoParse.applyPlan,pad]
  rw [write_stack_pad state.stack count ending shape size capacity]

theorem initial_pad (capacity ending : Nat) (inside : ending ≤ capacity) :
    ProtoParse.initial Word64.concrete ByteAuth.concrete capacity =
      pad (ProtoParse.initial Word64.concrete ByteAuth.concrete ending)
        (min 100 capacity-min 100 ending) := by
  have order : min 100 ending ≤ min 100 capacity := by omega
  simp only [ProtoParse.initial,pad]
  have append : List.replicate (min 100 ending) (Word64.concrete.const 0) ++
      List.replicate (min 100 capacity-min 100 ending) (0 : BitVec 64) =
      List.replicate (min 100 capacity) (Word64.concrete.const 0) := by
    change List.replicate (min 100 ending) (0 : BitVec 64) ++
      List.replicate (min 100 capacity-min 100 ending) (0 : BitVec 64) =
      List.replicate (min 100 capacity) (0 : BitVec 64)
    rw [←List.replicate_add,Nat.add_sub_of_le order]
  rw [append]

#print axioms lookup_append_zeros
#print axioms plan_pad
#print axioms cursor_pad
#print axioms write_stack_pad
#print axioms apply_pad
#print axioms initial_pad
end PrivateLengthV1.Stack
