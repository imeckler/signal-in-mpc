import SkipPlanWork.Fixed

namespace LibSignalReference.Candidate.ProstSkipPlan
open TlsMpc TlsMpc.Signal
open LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 500000

 theorem start_in_group (capacity : Nat)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hkey : key.ok = 255) (hvalue : key.value.toNat ≤ 4294967295)
    (htag : key.value >>> 3 ≠ 0) (hkind : key.value &&& 7 = 3)
    (hdepth : state.depth ≠ 0) (hlimit : state.depth.toNat ≤ 99) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok = 255 := by
  simp only [ProtoParse.plan,word_eq_value,Word64.ule_value]
  simp_all [Word64.concrete,ByteAuth.concrete,Word64.bor,Unpad.chooseByte,
    show (255#8) = BitVec.allOnes 8 by rfl, BitVec.and_allOnes,BitVec.allOnes_and,BitVec.xor_assoc]

/-- End tags are checked at depth100 too: they do not enter a child recursion. -/
theorem end_in_group (capacity : Nat)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hkey : key.ok = 255) (hvalue : key.value.toNat ≤ 4294967295)
    (htag : key.value >>> 3 ≠ 0) (hkind : key.value &&& 7 = 4)
    (hdepth : state.depth ≠ 0) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok =
      if key.value >>> 3 = ProtoParse.lookupWord Word64.concrete ByteAuth.concrete
        (state.depth - 1) 0 state.stack then 255 else 0 := by
  simp only [ProtoParse.plan,word_eq_value,Word64.ule_value]
  simp_all [Word64.concrete,ByteAuth.concrete,Word64.bor,Unpad.chooseByte,
    show (255#8) = BitVec.allOnes 8 by rfl, BitVec.and_allOnes,BitVec.allOnes_and,BitVec.xor_assoc]

theorem group_stop (capacity : Nat)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hkind : key.value &&& 7 = 3 ∨ key.value &&& 7 = 4) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).stop = key.stop := by
  rcases hkind with hkind | hkind <;>
    simp only [ProtoParse.plan,word_eq_value] <;>
    simp_all [Word64.concrete] <;>
    simp only [show (18446744073709551615#64) = BitVec.allOnes 64 by rfl,BitVec.allOnes_and]

theorem apply_start_depth (position : Nat)
    (plan : ProtoParse.Plan (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hs : state.ok = 255) (hp : plan.ok = 255)
    (hn : state.next = BitVec.ofNat 64 position) (hk : plan.kind = 3) :
    (ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position plan state).depth =
      state.depth + 1 := by
  simp only [ProtoParse.applyPlan,word_eq_value]
  simp_all [Word64.concrete,ByteAuth.concrete]
  simp only [show (18446744073709551615#64) = BitVec.allOnes 64 by rfl,BitVec.allOnes_and]

theorem apply_end_depth (position : Nat)
    (plan : ProtoParse.Plan (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hs : state.ok = 255) (hp : plan.ok = 255)
    (hn : state.next = BitVec.ofNat 64 position) (hk : plan.kind = 4) :
    (ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position plan state).depth =
      state.depth - 1 := by
  simp only [ProtoParse.applyPlan,word_eq_value]
  simp_all [Word64.concrete,ByteAuth.concrete]
  simp only [show (18446744073709551615#64) = BitVec.allOnes 64 by rfl,BitVec.allOnes_and]


theorem select_field_zero (yes no : ProtoParse.Field (BitVec 8) (BitVec 64)) :
    ProtoParse.selectField Word64.concrete ByteAuth.concrete 0 yes no = no := by
  cases no
  simp [ProtoParse.selectField,Word64.concrete,Unpad.chooseByte,ByteAuth.concrete,
    show (255#8) = BitVec.allOnes 8 by rfl,
    show (18446744073709551615#64) = BitVec.allOnes 64 by rfl,BitVec.allOnes_and]
  simp only [show (18446744073709551615#64) = BitVec.allOnes 64 by rfl,BitVec.allOnes_and,and_self]

theorem write_fields_zero (tag : BitVec 64) (payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (fields : List (ProtoParse.Field (BitVec 8) (BitVec 64))) :
    ProtoParse.writeFields Word64.concrete ByteAuth.concrete 0 tag payload fields = fields := by
  have hz (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  simp only [ProtoParse.writeFields,hz,select_field_zero]
  exact List.zipIdx_map_fst 0 fields

/-- Contents of unknown groups never overwrite recognized top-level message fields. -/
theorem nested_fields_unchanged (position : Nat)
    (plan : ProtoParse.Plan (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hdepth : state.depth ≠ 0) :
    (ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position plan state).fields = state.fields := by
  have ht : Word64.eq Word64.concrete ByteAuth.concrete state.depth (Word64.concrete.const 0) = 0 := by
    rw [word_eq_value]; exact if_neg hdepth
  have hz (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  simp only [ProtoParse.applyPlan,ht,hz,write_fields_zero]

theorem apply_next (position : Nat)
    (plan : ProtoParse.Plan (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hs : state.ok = 255) (hp : plan.ok = 255)
    (hn : state.next = BitVec.ofNat 64 position) :
    (ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position plan state).next = plan.stop := by
  simp only [ProtoParse.applyPlan,word_eq_value]
  simp_all [Word64.concrete,ByteAuth.concrete]
  simp only [show (18446744073709551615#64) = BitVec.allOnes 64 by rfl,BitVec.allOnes_and]


theorem write_stack_length (enabled : BitVec 8) (index tag : BitVec 64) (stack : List (BitVec 64)) :
    (ProtoParse.writeStack Word64.concrete ByteAuth.concrete enabled index tag stack).length = stack.length := by
  simp [ProtoParse.writeStack]

/-- The oblivious stack write changes precisely the selected index. -/
theorem write_stack_get (index tag : BitVec 64) (stack : List (BitVec 64))
    (i : Nat) (hi : i < stack.length) :
    (ProtoParse.writeStack Word64.concrete ByteAuth.concrete 255 index tag stack)[i]'(by
      rw [write_stack_length]; exact hi) =
      if index = BitVec.ofNat 64 i then tag else stack[i] := by
  simp only [ProtoParse.writeStack,List.getElem_map,List.getElem_zipIdx, Nat.zero_add,
    word_eq_value]
  by_cases h : index = BitVec.ofNat 64 i
  · have hc : index = Word64.concrete.const i := h
    simp only [if_pos hc,if_pos h]
    change Word64.concrete.select 255 tag stack[i] = tag
    exact Word64.select_accept _ _
  · have hc : index ≠ Word64.concrete.const i := h
    simp only [if_neg hc,if_neg h]
    change Word64.concrete.select 0 tag stack[i] = stack[i]
    exact Word64.select_reject _ _

#print axioms start_in_group
#print axioms end_in_group
#print axioms group_stop
#print axioms apply_start_depth
#print axioms apply_end_depth
#print axioms select_field_zero
#print axioms write_fields_zero
#print axioms nested_fields_unchanged
#print axioms apply_next
#print axioms write_stack_length
#print axioms write_stack_get
end LibSignalReference.Candidate.ProstSkipPlan
