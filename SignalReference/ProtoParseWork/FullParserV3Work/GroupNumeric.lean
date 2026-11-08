import ProtoParseWork.FullParserV3Work.Frames
import ProtoParseWork.FullParserV3Work.UnknownFields
import ProtoParseWork.FullParserV3Work.FieldTransition
import ProtoParseWork.FullParserV3Work.Numeric.TopPlan
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open LibSignalReference.Candidate.ProstSkipKey LibSignalReference.Candidate.ProstSkipPlan
open ParserErrorStateV2
set_option maxHeartbeats 2000000

theorem start_skip_plan (capacity : Nat) (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hk : key.ok = 255) (hr : key.value.toNat ≤ 4294967295) (ht : key.value >>> 3 ≠ 0)
    (hkind : key.value &&& 7 = 3) (hl : state.depth.toNat ≤ 99)
    (hskip : state.depth ≠ 0 ∨ 6 < (key.value >>> 3).toNat) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok = 255 := by
  by_cases hd : state.depth = 0
  · have hu : 6 < (key.value >>> 3).toNat := hskip.resolve_left (not_not.mpr hd)
    have hm : Word64.concrete.ule (Word64.concrete.shift key.value 3) (Word64.concrete.const 6) = 0 := by
      rw [Word64.ule_value]; exact if_neg (by change ¬(key.value >>> 3).toNat ≤ 6; omega)
    simp only [ProtoParse.plan,hm,word_eq_value,Word64.ule_value]
    simp_all [Word64.concrete,ByteAuth.concrete,Word64.bor,Unpad.chooseByte,
      show (255#8) = BitVec.allOnes 8 from rfl,BitVec.and_allOnes,BitVec.allOnes_and,BitVec.xor_assoc]
  · exact start_in_group capacity key payload state hk hr ht hkind hd hl

theorem apply_success_ok (position : Nat) (p : ProtoParse.Plan (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hs : state.ok = 255) (hp : p.ok = 255) (hn : state.next = BitVec.ofNat 64 position) :
    (ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state).ok = 255 := by
  have hh : Word64.eq Word64.concrete ByteAuth.concrete state.next (Word64.concrete.const position) = 255 := by
    rw [hn]; exact word_eq_self _
  simp only [ProtoParse.applyPlan,hs,hp,hh]
  rfl

theorem apply_start_stack (position : Nat) (p : ProtoParse.Plan (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hs : state.ok = 255) (hp : p.ok = 255) (hn : state.next = BitVec.ofNat 64 position) (hk : p.kind = 3) :
    (ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state).stack =
      ProtoParse.writeStack Word64.concrete ByteAuth.concrete 255 state.depth p.tag state.stack := by
  have hh : Word64.eq Word64.concrete ByteAuth.concrete state.next (Word64.concrete.const position) = 255 := by
    rw [hn]; exact word_eq_self _
  have ht : Word64.eq Word64.concrete ByteAuth.concrete p.kind (Word64.concrete.const 3) = 255 := by rw [hk]; decide
  simp only [ProtoParse.applyPlan,hs,hp,hh,ht]
  rfl

theorem apply_end_stack (position : Nat) (p : ProtoParse.Plan (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hk : p.kind = 4) :
    (ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state).stack = state.stack := by
  have ht : Word64.eq Word64.concrete ByteAuth.concrete p.kind (Word64.concrete.const 3) = 0 := by rw [hk]; decide
  have hz (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  simp only [ProtoParse.applyPlan,ht,hz,stack_zero]

theorem apply_skip_fields (position : Nat) (p : ProtoParse.Plan (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hs : state.ok = 255) (hp : p.ok = 255) (hn : state.next = BitVec.ofNat 64 position)
    (hl : state.fields.length ≤ 6) (hskip : state.depth ≠ 0 ∨ 6 < p.tag.toNat) :
    (ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state).fields = state.fields := by
  by_cases hd : state.depth = 0
  · rw [apply_top_success_fields state position p hs hn hd hp]
    exact write_unknown state.fields p.tag p.payload hl (hskip.resolve_left (not_not.mpr hd))
  · exact nested_fields_unchanged position p state hd

theorem apply_start_frames (position : Nat) (p : ProtoParse.Plan (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (tags : List U32) (tag : U32)
    (hf : Frames state.depth state.stack tags) (hb : tags.length < state.stack.length)
    (hs : state.ok = 255) (hp : p.ok = 255) (hn : state.next = BitVec.ofNat 64 position)
    (hk : p.kind = 3) (ht : p.tag = BitVec.ofNat 64 tag.val) :
    let result := ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state
    Frames result.depth result.stack (tags++[tag]) := by
  dsimp only
  simp only [apply_start_depth position p state hs hp hn hk,apply_start_stack position p state hs hp hn hk,ht]
  exact frames_push hf tag hb

theorem apply_end_frames (position : Nat) (p : ProtoParse.Plan (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (tags : List U32) (tag : U32)
    (hf : Frames state.depth state.stack (tags++[tag]))
    (hs : state.ok = 255) (hp : p.ok = 255) (hn : state.next = BitVec.ofNat 64 position) (hk : p.kind = 4) :
    let result := ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state
    Frames result.depth result.stack tags := by
  dsimp only
  simp only [apply_end_depth position p state hs hp hn hk,apply_end_stack position p state hk]
  exact frames_pop tag hf

#print axioms start_skip_plan
#print axioms apply_skip_fields
#print axioms apply_start_frames
#print axioms apply_end_frames
end FullParserV3
