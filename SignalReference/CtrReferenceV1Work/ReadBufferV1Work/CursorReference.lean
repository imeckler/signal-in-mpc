import CtrReferenceV1Work.ReadBufferV1Work.GeneratedOpaqueAttr.Funs
namespace LibSignalReference.Candidate.ReadBuffer16
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def position (p : Fin 16) : Usize := ⟨BitVec.ofNat _ (p.val+1)⟩
def cursor (p : Fin 16) : U8 := ⟨BitVec.ofNat 8 (p.val+1)⟩
def physical (head : U8) (tail : List U8) (length : tail.length=15) : ActualReadBuffer16.ReadBuffer :=
 ⟨⟨head::tail,by simpa [length]⟩⟩

theorem getter_valid (p : Fin 16) (tail : List U8) (length : tail.length=15) :
 ActualReadBuffer16.ReadBuffer.get_pos (physical (cursor p) tail length) = .ok (position p) := by
 rcases System.Platform.numBits_eq with h | h <;> fin_cases p <;>
 simp [ActualReadBuffer16.ReadBuffer.get_pos,physical,position,cursor,
  Array.index_usize,massert,lift,UScalar.cast,UScalar.ofNatCore,h]
 all_goals simp only [UScalar.val, UScalarTy.numBits, h, BitVec.toNat_ofNat, Nat.zero_mod]
 all_goals norm_num [h]
 all_goals rfl

theorem position_val (p : Fin 16) : (position p).val = p.val+1 := by
 simp only [position,UScalar.val,BitVec.toNat_ofNat,UScalarTy.numBits]
 apply Nat.mod_eq_of_lt
 rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> norm_num <;> omega

theorem cursor_val (p : Fin 16) : (cursor p).val = p.val+1 := by
 simp only [cursor,UScalar.val,BitVec.toNat_ofNat,UScalarTy.numBits]
 apply Nat.mod_eq_of_lt
 have hp := p.isLt
 omega

theorem cast_position (p : Fin 16) : UScalar.cast .U8 (position p) = cursor p := by
 apply UScalar.eq_of_val_eq
 rw [UScalar.cast_val_eq,position_val,cursor_val]
 apply Nat.mod_eq_of_lt
 have hp := p.isLt
 change p.val+1 < 256
 omega

theorem update_head (head byte : U8) (tail : List U8) (length : tail.length=15) :
 Array.update (physical head tail length).buffer 0#usize byte =
 .ok (physical byte tail length).buffer := by
 have hz : (0#usize).val = 0 := by
  simp only [UScalar.val,UScalar.ofNatCore,BitVec.toNat_ofNat,Nat.zero_mod]
  rfl
 simp only [Array.update,Array.getElem?_Usize_eq,physical,hz,List.getElem?_cons_zero]
 rfl

theorem set_cursor (p : Fin 16) (head : U8) (tail : List U8) (length : tail.length=15) :
 ActualReadBuffer16.ReadBuffer.set_pos_unchecked (physical head tail length) (position p) =
 .ok (physical (cursor p) tail length) := by
 have hz : (0#usize).val = 0 := by
  simp only [UScalar.val,UScalar.ofNatCore,BitVec.toNat_ofNat,Nat.zero_mod]
  rfl
 have hn : position p ≠ 0#usize := by
  intro heq
  have hval := congrArg UScalar.val heq
  rw [position_val,hz] at hval
  omega
 have hle : position p ≤ 16#usize := by
  change (position p).val ≤ (16#usize).val
  rw [position_val]
  change p.val+1 ≤ 16
  omega
 have ha : (massert (position p != 0#usize) : Result Unit) = .ok () := by
  simp [massert,hn]
 have hb : (massert (position p <= 16#usize) : Result Unit) = .ok () := by
  simp [massert,hle]
 simp only [ActualReadBuffer16.ReadBuffer.set_pos_unchecked,ha,hb,bind_tc_ok,
  cast_position,lift,update_head]

theorem reset_exhausts (head : U8) (tail : List U8) (length : tail.length=15) :
 ActualReadBuffer16.ReadBuffer.reset (physical head tail length) =
 .ok (physical (cursor ⟨15,by decide⟩) tail length) := by
 simp only [ActualReadBuffer16.ReadBuffer.reset,update_head,bind_tc_ok]
 rfl

def available (p : Fin 16) : Usize := ⟨BitVec.ofNat _ (15-p.val)⟩

theorem available_val (p : Fin 16) : (available p).val = 15-p.val := by
 simp only [available,UScalar.val,BitVec.toNat_ofNat,UScalarTy.numBits]
 apply Nat.mod_eq_of_lt
 rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> norm_num <;> omega

theorem remaining_actual (p : Fin 16) (tail : List U8) (length : tail.length=15) :
 ActualReadBuffer16.ReadBuffer.remaining (physical (cursor p) tail length) = .ok (available p) := by
 simp only [ActualReadBuffer16.ReadBuffer.remaining,ActualReadBuffer16.ReadBuffer.size,
  getter_valid,bind_tc_ok]
 change UScalar.sub (16#usize) (position p) = .ok (available p)
 have h16 : (16#usize).val = 16 := rfl
 have hn : ¬ (16 < p.val+1) := by omega
 simp only [UScalar.sub,h16,position_val,hn,if_false,available]
 have hv : 16-(p.val+1) = 15-p.val := by omega
 rw [hv]

def count (p : Fin 16) (requested : Usize) : Usize :=
 core.cmp.impls.OrdUsize.min (available p) requested

theorem count_val (p : Fin 16) (requested : Usize) :
 (count p requested).val = min (15-p.val) requested.val := by
 simp only [count,core.cmp.impls.OrdUsize.min_val,available_val]

def advance (p : Fin 16) (requested : Usize) : Fin 16 :=
 ⟨p.val+(count p requested).val,by
  rw [count_val]
  have h := Nat.min_le_left (15-p.val) requested.val
  omega⟩

theorem add_position (p : Fin 16) (requested : Usize) :
 ((position p + count p requested) : Result Usize) = .ok (position (advance p requested)) := by
 have hpos := position_val p
 have hbound : (position p).val + (count p requested).val ≤ 16 := by
  rw [hpos,count_val]
  have h := Nat.min_le_left (15-p.val) requested.val
  omega
 have spec := UScalar.add_equiv (position p) (count p requested)
 generalize hcall : ((position p + count p requested) : Result Usize) = out at spec
 cases out with
 | ok z =>
   have hz : z = position (advance p requested) := by
    apply UScalar.eq_of_val_eq
    rw [position_val]
    have hv := spec.2.1
    simp only [advance,Fin.val_mk] at *
    omega
   simpa only [hz] using hcall
 | fail error =>
   exfalso
   apply spec
   scalar_tac
 | div => exact False.elim spec

theorem minimum_actual (p : Fin 16) (requested : Usize) :
 core.cmp.min core.cmp.OrdUsize (available p) requested = .ok (count p requested) := rfl

theorem read_cached_actual (p : Fin 16) (requested : Usize)
 (tail : List U8) (length : tail.length=15) :
 ∃ result, ActualReadBuffer16.ReadBuffer.read_cached (physical (cursor p) tail length) requested =
  .ok (result,physical (cursor (advance p requested)) tail length) ∧
 result.val = (tail.drop p.val).take (min (15-p.val) requested.val) := by
 simp only [ActualReadBuffer16.ReadBuffer.read_cached,remaining_actual,getter_valid,
  minimum_actual,add_position,set_cursor,bind_tc_ok]
 have hfit : 15 ≤ 15-p.val+p.val := by omega
 simp [hfit,core.array.Array.index,core.ops.index.IndexSlice,core.slice.index.Slice.index,
  core.slice.index.SliceIndexRangeFromUsizeSlice,core.slice.index.SliceIndexRangeFromUsizeSlice.index,
  core.slice.index.SliceIndexRangeToUsizeSlice,core.slice.index.SliceIndexRangeToUsizeSlice.index,
  physical,Array.to_slice,Slice.drop,Slice.length,position_val,count_val,length,List.slice]

def unread (p : Fin 16) (tail : List U8) : List U8 := tail.drop p.val

theorem advance_unread (p : Fin 16) (requested : Usize) (tail : List U8) :
 unread (advance p requested) tail =
 (unread p tail).drop (min (15-p.val) requested.val) := by
 simp only [unread,advance,Fin.val_mk,count_val,List.drop_drop]

theorem read_cached_logical (p : Fin 16) (requested : Usize)
 (tail : List U8) (length : tail.length=15) :
 ∃ result, ActualReadBuffer16.ReadBuffer.read_cached (physical (cursor p) tail length) requested =
  .ok (result,physical (cursor (advance p requested)) tail length) ∧
 result.val = (unread p tail).take requested.val ∧
 unread (advance p requested) tail =
 (unread p tail).drop (min (unread p tail).length requested.val) := by
 obtain ⟨result,hr,hv⟩ := read_cached_actual p requested tail length
 have hlen : (tail.drop p.val).length = 15-p.val := by simp [length]
 refine ⟨result,hr,?_,?_⟩
 · rw [hv]
   unfold unread
   by_cases h : requested.val ≤ 15-p.val
   · rw [Nat.min_eq_right h]
   · rw [Nat.min_eq_left (by omega)]
     rw [List.take_of_length_le (by omega),List.take_of_length_le (by omega)]
 · simpa only [unread,hlen] using advance_unread p requested tail

end LibSignalReference.Candidate.ReadBuffer16
