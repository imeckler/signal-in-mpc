import CtrReferenceV1Work.WriteBufferV1Work.Generated.Funs
import CtrReferenceV1Work.ReadBufferV1Work.CursorReference
namespace LibSignalReference.Candidate.WriteBuffer16
open Aeneas Aeneas.Std
open LibSignalReference.Candidate
set_option maxHeartbeats 2000000

def physical (head : U8) (tail : List U8) (ht : tail.length=15) : ActualWriteBuffer16.ReadBuffer :=
 ⟨(ReadBuffer16.physical head tail ht).buffer⟩

theorem setter (p : Fin 16) (head : U8) (tail : List U8) (ht : tail.length=15) :
 ActualWriteBuffer16.ReadBuffer.set_pos_unchecked (physical head tail ht) (ReadBuffer16.position p) =
 .ok (physical (ReadBuffer16.cursor p) tail ht) := by
 have hz : (0#usize).val = 0 := by
  simp only [UScalar.val,UScalar.ofNatCore,BitVec.toNat_ofNat,Nat.zero_mod]
  rfl
 have hn : ReadBuffer16.position p ≠ 0#usize := by
  intro heq
  have hval := congrArg UScalar.val heq
  rw [ReadBuffer16.position_val,hz] at hval
  omega
 have hle : ReadBuffer16.position p ≤ 16#usize := by
  change (ReadBuffer16.position p).val ≤ (16#usize).val
  rw [ReadBuffer16.position_val]
  change p.val+1 ≤ 16
  omega
 have ha : (massert (ReadBuffer16.position p != 0#usize) : Result Unit) = .ok () := by
  simp [massert,hn]
 have hb : (massert (ReadBuffer16.position p <= 16#usize) : Result Unit) = .ok () := by
  simp [massert,hle]
 simp only [ActualWriteBuffer16.ReadBuffer.set_pos_unchecked,ha,hb,bind_tc_ok,
  ReadBuffer16.cast_position,lift,physical,ReadBuffer16.update_head]

theorem reset (head : U8) (tail : List U8) (ht : tail.length=15) :
 ActualWriteBuffer16.ReadBuffer.reset (physical head tail ht) =
 .ok (physical (ReadBuffer16.cursor ⟨15,by decide⟩) tail ht) := by
 simp only [ActualWriteBuffer16.ReadBuffer.reset,physical,ReadBuffer16.update_head,bind_tc_ok]
 rfl

theorem drop_resets (head : U8) (tail : List U8) (ht : tail.length=15) :
 ActualWriteBuffer16.ResetGuard.Insts.CoreOpsDropDrop.drop (physical head tail ht) =
 .ok (physical (ReadBuffer16.cursor ⟨15,by decide⟩) tail ht,fun value => value) := by
 simp only [ActualWriteBuffer16.ResetGuard.Insts.CoreOpsDropDrop.drop,reset,bind_tc_ok]

abbrev Generator (G : Type) := ActualWriteBuffer16.core.ops.function.FnOnce G (Array U8 16#usize) Unit
abbrev Reader (R : Type) := ActualWriteBuffer16.core.ops.function.FnOnce R (Slice U8) Unit

theorem write_zero {G R : Type} (generator : Generator G) (reader : Reader R)
 (self : ActualWriteBuffer16.ReadBuffer) (g : G) (r : R) :
 ActualWriteBuffer16.ReadBuffer.write_block generator reader self 0#usize g r = .ok self := by
 simp [ActualWriteBuffer16.ReadBuffer.write_block,massert]

theorem write_success {G R : Type} (generator : Generator G) (reader : Reader R)
 (self : ActualWriteBuffer16.ReadBuffer) (g : G) (r : R) (p : Fin 15)
 (head : U8) (tail : List U8) (ht : tail.length=15) (observed : Slice U8)
 (generated : generator.call_once g self.buffer = .ok ((),(physical head tail ht).buffer))
 (prefix_read : core.array.Array.index (core.ops.index.IndexSlice
   (core.slice.index.SliceIndexRangeToUsizeSlice U8)) (physical head tail ht).buffer
    {«end»:=ReadBuffer16.position ⟨p.val,by omega⟩} = .ok observed)
 (consumed : reader.call_once r observed = .ok ()) :
 ActualWriteBuffer16.ReadBuffer.write_block generator reader self
  (ReadBuffer16.position ⟨p.val,by omega⟩) g r =
 .ok (physical (ReadBuffer16.cursor ⟨p.val,by omega⟩) tail ht) := by
 have hn : ReadBuffer16.position ⟨p.val,by omega⟩ ≠ 0#usize := by
  intro h
  have hv := congrArg UScalar.val h
  rw [ReadBuffer16.position_val] at hv
  change p.val+1=0 at hv
  omega
 have hlt : ReadBuffer16.position ⟨p.val,by omega⟩ < 16#usize := by
  change (ReadBuffer16.position ⟨p.val,by omega⟩).val < 16
  rw [ReadBuffer16.position_val]
  have hp := p.isLt
  change p.val+1 < 16
  omega
 simp only [ActualWriteBuffer16.ReadBuffer.write_block]
 have ha : (massert ((ReadBuffer16.position ⟨p.val,by omega⟩ = 0#usize) ||
    (ReadBuffer16.position ⟨p.val,by omega⟩ < 16#usize)) : Result Unit) = .ok () := by
  simp [massert,hn,hlt]
 rw [ha]
 simp only [bind_tc_ok,hn,if_false]
 rw [generated]
 dsimp only [Bind.bind,Aeneas.Std.bind,uncurry]
 rw [prefix_read]
 simp only [bind_tc_ok,bind_ok]
 rw [consumed]
 simp only [bind_tc_ok,bind_ok,ActualWriteBuffer16.core.mem.forget]
 exact setter ⟨p.val,by omega⟩ head tail ht


theorem write_oversized {G R : Type} (generator : Generator G) (reader : Reader R)
 (self : ActualWriteBuffer16.ReadBuffer) (g : G) (r : R) (readLen : Usize)
 (large : 16 ≤ readLen.val) :
 ActualWriteBuffer16.ReadBuffer.write_block generator reader self readLen g r =
 .fail .assertionFailure := by
 have hn : readLen ≠ 0#usize := by
  intro h
  have hv := congrArg UScalar.val h
  change readLen.val = 0 at hv
  omega
 have hlt : ¬ (readLen < 16#usize) := by
  change ¬ (readLen.val < 16)
  omega
 simp [ActualWriteBuffer16.ReadBuffer.write_block,massert,hn,hlt]

end LibSignalReference.Candidate.WriteBuffer16
