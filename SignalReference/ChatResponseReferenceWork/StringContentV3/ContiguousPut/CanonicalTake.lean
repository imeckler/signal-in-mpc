import ChatResponseReferenceWork.StringContentV3.ContiguousPut.LoopLowering
import BytesReferenceWork.CopyModel
open Aeneas Aeneas.Std Result ControlFlow ProstAdapterCandidate
namespace ChatResponseReference.ContiguousPut
open LibSignalReference.Candidate.ProstBytesBuf
/-- Executable contiguous Take content; cursor and remaining limit are separate
observations. Source-level field/trait projection is composed independently. -/
structure TakeState where
  inner : Slice U8
  limit : Usize
def view (s : TakeState) : Slice U8 := ProstBytesCandidate.ContentModel.take s.inner s.limit.val
def subtractLimit (limit count : Usize) : Usize :=
  Usize.ofNatCore (limit.val-count.val)
    (Nat.lt_of_le_of_lt (Nat.sub_le _ _) limit.bv.isLt)
theorem subtractLimit_val (limit count : Usize) :
    (subtractLimit limit count).val = limit.val-count.val := UScalar.ofNatCore_val_eq _
def after (s : TakeState) : TakeState :=
  ⟨drop s.inner (view s).length,subtractLimit s.limit (view s).len⟩
def takeAdvance (s : TakeState) (count : Usize) : Result TakeState :=
  if count.val ≤ s.limit.val ∧ count.val ≤ s.inner.length then
    .ok ⟨drop s.inner count.val,subtractLimit s.limit count⟩ else .fail .panic
def takeBuf : bytes.buf.buf_impl.Buf TakeState where
  remaining := fun s => .ok (view s).len
  chunk := fun s => .ok (view s)
  advance := takeAdvance
  has_remaining := fun s => .ok (0 < (view s).length)
theorem view_length (s : TakeState) : (view s).length = min s.limit.val s.inner.length :=
  List.length_take
theorem view_bounds (s : TakeState) : (view s).length ≤ s.limit.val ∧
    (view s).length ≤ s.inner.length := by rw [view_length]; exact ⟨Nat.min_le_left _ _,Nat.min_le_right _ _⟩
theorem take_advance_view (s : TakeState) : takeBuf.advance s (view s).len = .ok (after s) := by
  change takeAdvance s (view s).len = _
  unfold takeAdvance
  rw [if_pos (by simpa only [Slice.len_val] using view_bounds s)]
  rfl
theorem after_empty (s : TakeState) : (view (after s)).length = 0 := by
  rw [view_length]
  change min (subtractLimit s.limit (view s).len).val
    (drop s.inner (view s).length).length = 0
  rw [subtractLimit_val,Slice.len_val,drop_length,view_length]
  omega
theorem take_exhausted (s : TakeState) : takeBuf.has_remaining (after s) = .ok false := by
  change Aeneas.Std.Result.ok (decide (0 < (view (after s)).length)) = _
  rw [after_empty]
  rfl
/-- Derive the lowering condition from the actual native loop body's operations
and contiguous bounds, including vector-extension failures. -/
theorem canonical_stop (value : alloc.vec.Vec U8) (s : TakeState)
    (output : alloc.vec.Vec U8) (rest : TakeState)
    (step : alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put_loop.body takeBuf value s =
      .ok (.cont (output,rest))) : takeBuf.has_remaining rest = .ok false := by
  by_cases empty : (view s).length = 0
  · unfold alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put_loop.body at step
    have hh : takeBuf.has_remaining s = .ok false := by change Aeneas.Std.Result.ok (decide (0 < (view s).length)) = _; rw [empty]; rfl
    rw [hh] at step
    simp only [bind_tc_ok,Bool.false_eq_true,if_false] at step
    cases step
  · have hh : takeBuf.has_remaining s = .ok true := by
      change Aeneas.Std.Result.ok (decide (0 < (view s).length)) = _
      congr 1
      exact decide_eq_true_eq.mpr (by omega)
    have suffix := body_suffix takeBuf value s (after s) (view s) hh rfl
      (take_advance_view s) output rest step
    rw [suffix]
    exact take_exhausted s
/-- For every input and limit, the actual loop equals the guarded single-body
lowering. There is no primitive termination or success-only assumption. -/
theorem canonical_lowering (value : alloc.vec.Vec U8) (s : TakeState) :
    alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put_loop takeBuf value s =
      singleLoop takeBuf value s :=
  loop_lowering takeBuf value s (canonical_stop value s)
#print axioms take_advance_view
#print axioms canonical_stop
#print axioms canonical_lowering
end ChatResponseReference.ContiguousPut
