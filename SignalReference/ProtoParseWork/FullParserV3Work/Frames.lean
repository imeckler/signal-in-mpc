import ProtoParseWork.FullParserV3Work.Numeric.GroupReference
import ProtoParseWork.FullParserV3Work.Intervals
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open LibSignalReference.Candidate.ProstSkipPlan
set_option maxHeartbeats 2000000

/-- Only the live prefix of the oblivious stack represents Rust group frames;
popped cells remain private scratch space. Frame order is outermost first. -/
structure Frames (depth : BitVec 64) (stack : List (BitVec 64)) (tags : List U32) : Prop where
  depth_eq : depth = BitVec.ofNat 64 tags.length
  bound : tags.length ≤ stack.length
  limit : stack.length ≤ 100
  entries : ∀ i (hi : i < tags.length), stack[i]'(by omega) = BitVec.ofNat 64 tags[i].val

theorem small_word_eq (left right : Nat) (hl : left ≤ 100) (hr : right ≤ 100) :
    BitVec.ofNat 64 left = BitVec.ofNat 64 right ↔ left = right := by
  constructor
  · intro h
    have hn := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : left < 2^64),
      Nat.mod_eq_of_lt (by omega : right < 2^64)] at hn
    exact hn
  · rintro rfl; rfl

theorem frames_push {depth : BitVec 64} {stack : List (BitVec 64)} {tags : List U32}
    (h : Frames depth stack tags) (tag : U32) (hb : tags.length < stack.length) :
    Frames (depth+1) (ProtoParse.writeStack Word64.concrete ByteAuth.concrete 255 depth
      (BitVec.ofNat 64 tag.val) stack) (tags++[tag]) := by
  have hlim := h.limit
  constructor
  case depth_eq =>
    rw [h.depth_eq,List.length_append,List.length_singleton,BitVec.ofNat_add]
    rfl
  case bound =>
    rw [write_stack_length,List.length_append,List.length_singleton]; omega
  case limit =>
    rw [write_stack_length]; exact h.limit
  case entries =>
    intro i hi
    have hi' : i < stack.length := by simp only [List.length_append,List.length_singleton] at hi; omega
    rw [write_stack_get depth _ stack i hi',h.depth_eq]
    by_cases he : i = tags.length
    · subst i
      simp only [if_true,List.getElem_append_right («as» := tags) (bs := [tag]) (i := tags.length) (Nat.le_refl _),Nat.sub_self,List.getElem_cons_zero]
    · have hit : i < tags.length := by simp only [List.length_append,List.length_singleton] at hi; omega
      have hn : BitVec.ofNat 64 tags.length ≠ BitVec.ofNat 64 i := by
        intro hh
        have hv := (small_word_eq tags.length i (by omega) (by omega)).mp hh
        omega
      rw [if_neg hn,h.entries i hit,List.getElem_append_left hit]

theorem frames_pop {depth : BitVec 64} {stack : List (BitVec 64)} {tags : List U32} (tag : U32)
    (h : Frames depth stack (tags++[tag])) : Frames (depth-1) stack tags := by
  constructor
  case depth_eq =>
    rw [h.depth_eq,List.length_append,List.length_singleton,BitVec.ofNat_add]
    simp only [show BitVec.ofNat 64 1 = (1 : BitVec 64) from rfl,add_sub_cancel_right]
  case bound =>
    have hb := h.bound
    simp only [List.length_append,List.length_singleton] at hb
    omega
  case limit =>
    exact h.limit
  case entries =>
    intro i hi
    have he := h.entries i (by simp only [List.length_append,List.length_singleton]; omega)
    simpa only [List.getElem_append_left hi] using he

theorem frames_top {depth : BitVec 64} {stack : List (BitVec 64)} {tags : List U32} (tag : U32)
    (h : Frames depth stack (tags++[tag])) :
    ProtoParse.lookupWord Word64.concrete ByteAuth.concrete (depth-1) 0 stack = BitVec.ofNat 64 tag.val := by
  have hb : tags.length+1 ≤ 100 := by simpa only [List.length_append,List.length_singleton] using h.bound.trans h.limit
  have hstack : tags.length+1 ≤ stack.length := by simpa only [List.length_append,List.length_singleton] using h.bound
  have hd : depth.toNat = tags.length+1 := by
    have hsmall : (tags++[tag]).length < 2^64 := by simp only [List.length_append,List.length_singleton]; omega
    rw [h.depth_eq,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hsmall]
    simp only [List.length_append,List.length_singleton]
  have he := lookup_current_group ⟨255,0,depth,stack,[]⟩ (by simp only; omega) (by simp only; omega) h.limit
  dsimp only at he
  rw [he]
  have hi : depth.toNat-1 = tags.length := by omega
  simp only [hi]
  have ht := h.entries tags.length (by simp)
  simpa only [List.getElem_append_right («as» := tags) (bs := [tag]) (i := tags.length) (Nat.le_refl _),Nat.sub_self,List.getElem_cons_zero] using ht

#print axioms frames_push
#print axioms frames_pop
#print axioms frames_top
end FullParserV3
