import BytesReferenceWork.VecReference
open Aeneas Aeneas.Std Result ControlFlow ProstAdapterCandidate
namespace ChatResponseReference.ContiguousPut
/-- Execute the actual source body once. A remaining nonempty buffer is an
explicit unsupported-domain failure, not an assumed successful copy. -/
noncomputable def singleLoop {B : Type} (inst : bytes.buf.buf_impl.Buf B)
    (value : alloc.vec.Vec U8) (input : B) : Result (alloc.vec.Vec U8) := do
  let step ← alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put_loop.body inst value input
  match step with
  | .done output => .ok output
  | .cont (output,rest) =>
    let more ← inst.has_remaining rest
    if more then .fail .panic else .ok output
/-- Exact loop lowering for the supported one-chunk domain. First-body failures,
divergence and empty input remain present. The only condition is exhaustion
following a successful body; canonical contiguous buffers discharge it below. -/
theorem loop_lowering {B : Type} (inst : bytes.buf.buf_impl.Buf B)
    (value : alloc.vec.Vec U8) (input : B)
    (exhausted : ∀ output rest,
      alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put_loop.body inst value input =
        .ok (.cont (output,rest)) → inst.has_remaining rest = .ok false) :
    alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put_loop inst value input =
      singleLoop inst value input := by
  rw [alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put_loop,loop.eq_1]
  unfold singleLoop
  simp only [uncurry_apply_pair]
  cases first : alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put_loop.body inst value input <;>
    simp only [first,bind_tc_ok,bind_tc_fail,bind_tc_div]
  rename_i step
  cases step with
  | done output => rfl
  | cont pair =>
    rcases pair with ⟨output,rest⟩
    change alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put_loop inst output rest = (do
      let more ← inst.has_remaining rest
      if more then .fail .panic else .ok output)
    rw [exhausted output rest first]
    change alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put_loop inst output rest = .ok output
    exact LibSignalReference.Candidate.ProstVecAdapter.put_loop_done inst output rest
      (exhausted output rest first)
/-- Source-body suffix witness: every successful iteration copies the supplied
chunk and ends at the exact advanced buffer. No success premise is imposed on
the vector extension; its failure/divergence cases are retained. -/
theorem body_suffix {B : Type} (inst : bytes.buf.buf_impl.Buf B)
    (value : alloc.vec.Vec U8) (input final : B) (view : Slice U8)
    (hh : inst.has_remaining input = .ok true)
    (hc : inst.chunk input = .ok view)
    (ha : inst.advance input view.len = .ok final)
    (output : alloc.vec.Vec U8) (rest : B)
    (step : alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put_loop.body inst value input =
      .ok (.cont (output,rest))) : rest = final := by
  unfold alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put_loop.body at step
  rw [hh] at step
  simp only [bind_tc_ok,if_true,hc] at step
  cases extend : Aeneas.Std.alloc.vec.Vec.extend_from_slice core.clone.CloneU8 value view <;>
    simp only [extend,bind_tc_ok,bind_tc_fail,bind_tc_div,ha] at step
  all_goals cases step
  rfl
#print axioms loop_lowering
#print axioms body_suffix
end ChatResponseReference.ContiguousPut
