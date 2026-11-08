import ProtoParseWork.DispatcherIntegrationWork.FieldDispatch
open Aeneas Aeneas.Std Result
open SignalMessageIntegration
set_option linter.unusedSimpArgs false
namespace DispatcherIntegration
set_option maxHeartbeats 1000000

/-- Adapter projection keeps precisely the accepted contiguous get_u8 behavior. -/
theorem field_slice_adapter : toFieldBuf sliceBuf =
    LibSignalReference.Candidate.ProstFieldBuf.sliceBuf := rfl

theorem bytes_slice_adapter : toBytesBuf sliceBuf =
    LibSignalReference.Candidate.ProstBytesBuf.sliceBuf := by
  change { LibSignalReference.Candidate.ProstBytesBuf.sliceBuf with
    copy_to_bytes := (toBytesBuf sliceBuf).copy_to_bytes } = _
  suffices hc : (toBytesBuf sliceBuf).copy_to_bytes =
      LibSignalReference.Candidate.ProstBytesBuf.sliceBuf.copy_to_bytes by rw [hc]
  funext view n
  by_cases hn : n.val ≤ view.length
  · have hp : ¬ n > view.len := by scalar_tac
    simp [toBytesBuf, sliceBuf,
      ProstBytesCandidate.bytes.buf.buf_impl.Buf.copy_to_bytes.default,
      ProstBytesCandidate.ContentModel.copySlice,
      LibSignalReference.Candidate.ProstBytesBuf.sliceBuf,
      LibSignalReference.Candidate.ProstBytesBuf.remaining,
      LibSignalReference.Candidate.ProstBytesBuf.chunk,
      LibSignalReference.Candidate.ProstBytesBuf.advance, hn, hp,
      Nat.not_lt.mpr hn]
    rfl
  · have hp : n > view.len := by scalar_tac
    simp [toBytesBuf, sliceBuf,
      ProstBytesCandidate.bytes.buf.buf_impl.Buf.copy_to_bytes.default,
      ProstBytesCandidate.ContentModel.copySlice,
      LibSignalReference.Candidate.ProstBytesBuf.sliceBuf,
      LibSignalReference.Candidate.ProstBytesBuf.remaining, hn, hp]

/-- The generated Vec adapter's replacement slot is the extracted actual Vec
replacement. The other dictionary slots are retained in the unused parameter. -/
theorem bytes_actual_adapter :
    toBytesAdapter alloc.vec.VecU8.Insts.ProstEncodingBytesAdapter =
    LibSignalReference.Candidate.ProstBytes.withActualReplace
      (toBytesAdapter alloc.vec.VecU8.Insts.ProstEncodingBytesAdapter).sealedBytesAdapterInst := rfl

def fieldStatus (r : core.result.Result Unit ProstFieldCandidate.error.DecodeError) :
    core.result.Result Unit prost.error.DecodeError :=
  match r with | .Ok x => .Ok x | .Err e => .Err (fieldError e)

/-- Every contiguous scalar input has the accepted exact prefix/error behavior;
no decoder-equality premise is supplied by the caller. -/
theorem counter_full_reference (m : proto.wire.SignalMessage) (before : Slice U8)
    (ctx : prost.encoding.DecodeContext) :
    ∃ decoded after,
      LibSignalReference.Candidate.ProstFieldBuf.PrefixPost before decoded after ∧
      LibSignalReference.Candidate.ProstFieldBuf.ErrorPost before decoded after ∧
      proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
        sliceBuf m 2#u32 .Varint before ctx =
      (let (status,value,suffix) := LibSignalReference.Candidate.ProstField.scalarResult
        (m.counter.getD 0#u32) decoded after
       ok (fieldStatus status,{m with counter := some value},suffix)) := by
  obtain ⟨decoded,after,hp,he,hm⟩ :=
    LibSignalReference.Candidate.ProstField.uint32_full_reference before (m.counter.getD 0#u32) ⟨ctx.recurse_count⟩
  refine ⟨decoded,after,hp,he,?_⟩
  rw [counter_dispatch]
  unfold prost.encoding.uint32.merge
  rw [field_slice_adapter]
  simp only [toFieldWire]
  rw [hm]
  cases decoded <;> rfl

/-- Every contiguous bytes input has accepted exact length/error/suffix behavior;
the allocation/content assumptions are inherited from BytesReferenceWork. -/
theorem ratchet_key_full_reference (m : proto.wire.SignalMessage) (before : Slice U8)
    (ctx : prost.encoding.DecodeContext) :
    ∃ decoded after,
      LibSignalReference.Candidate.ProstBytesBuf.PrefixPost before decoded after ∧
      LibSignalReference.Candidate.ProstBytesBuf.ErrorPost before decoded after ∧
      proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
        sliceBuf m 1#u32 .LengthDelimited before ctx =
      (let (status,value,suffix) := LibSignalReference.Candidate.ProstBytes.bytesResult
        (m.ratchet_key.getD (alloc.vec.Vec.new U8)) decoded after
       ok (status,{m with ratchet_key := some value},suffix)) := by
  obtain ⟨decoded,after,hp,he,hm⟩ :=
    LibSignalReference.Candidate.ProstBytes.bytes_full_reference
      (toBytesAdapter alloc.vec.VecU8.Insts.ProstEncodingBytesAdapter).sealedBytesAdapterInst
      before (m.ratchet_key.getD (alloc.vec.Vec.new U8)) ctx
  refine ⟨decoded,after,hp,he,?_⟩
  rw [ratchet_key_dispatch]
  unfold prost.encoding.bytes.merge
  rw [bytes_slice_adapter,bytes_actual_adapter]
  change (do
    let (status,value,suffix) ← ProstBytesCandidate.encoding.bytes.merge
      (LibSignalReference.Candidate.ProstBytes.withActualReplace
        (toBytesAdapter alloc.vec.VecU8.Insts.ProstEncodingBytesAdapter).sealedBytesAdapterInst)
      LibSignalReference.Candidate.ProstBytesBuf.sliceBuf .LengthDelimited
      (m.ratchet_key.getD (alloc.vec.Vec.new U8)) before ctx
    ok (status,{m with ratchet_key := some value},suffix)) = _
  rw [hm]
  cases decoded <;> simp only [bind_tc_ok]
theorem previous_counter_full_reference (m : proto.wire.SignalMessage) (before : Slice U8)
    (ctx : prost.encoding.DecodeContext) :
    ∃ decoded after,
      LibSignalReference.Candidate.ProstFieldBuf.PrefixPost before decoded after ∧
      LibSignalReference.Candidate.ProstFieldBuf.ErrorPost before decoded after ∧
      proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
        sliceBuf m 3#u32 .Varint before ctx =
      (let (status,value,suffix) := LibSignalReference.Candidate.ProstField.scalarResult
        (m.previous_counter.getD 0#u32) decoded after
       ok (fieldStatus status,{m with previous_counter := some value},suffix)) := by
  obtain ⟨decoded,after,hp,he,hm⟩ :=
    LibSignalReference.Candidate.ProstField.uint32_full_reference before (m.previous_counter.getD 0#u32) ⟨ctx.recurse_count⟩
  refine ⟨decoded,after,hp,he,?_⟩
  rw [previous_counter_dispatch]
  unfold prost.encoding.uint32.merge
  rw [field_slice_adapter]
  simp only [toFieldWire]
  rw [hm]
  cases decoded <;> rfl

theorem ciphertext_full_reference (m : proto.wire.SignalMessage) (before : Slice U8)
    (ctx : prost.encoding.DecodeContext) :
    ∃ decoded after,
      LibSignalReference.Candidate.ProstBytesBuf.PrefixPost before decoded after ∧
      LibSignalReference.Candidate.ProstBytesBuf.ErrorPost before decoded after ∧
      proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
        sliceBuf m 4#u32 .LengthDelimited before ctx =
      (let (status,value,suffix) := LibSignalReference.Candidate.ProstBytes.bytesResult
        (m.ciphertext.getD (alloc.vec.Vec.new U8)) decoded after
       ok (status,{m with ciphertext := some value},suffix)) := by
  obtain ⟨decoded,after,hp,he,hm⟩ :=
    LibSignalReference.Candidate.ProstBytes.bytes_full_reference
      (toBytesAdapter alloc.vec.VecU8.Insts.ProstEncodingBytesAdapter).sealedBytesAdapterInst
      before (m.ciphertext.getD (alloc.vec.Vec.new U8)) ctx
  refine ⟨decoded,after,hp,he,?_⟩
  rw [ciphertext_dispatch]
  unfold prost.encoding.bytes.merge
  rw [bytes_slice_adapter,bytes_actual_adapter]
  change (do
    let (status,value,suffix) ← ProstBytesCandidate.encoding.bytes.merge
      (LibSignalReference.Candidate.ProstBytes.withActualReplace
        (toBytesAdapter alloc.vec.VecU8.Insts.ProstEncodingBytesAdapter).sealedBytesAdapterInst)
      LibSignalReference.Candidate.ProstBytesBuf.sliceBuf .LengthDelimited
      (m.ciphertext.getD (alloc.vec.Vec.new U8)) before ctx
    ok (status,{m with ciphertext := some value},suffix)) = _
  rw [hm]
  cases decoded <;> simp only [bind_tc_ok]
theorem pq_ratchet_full_reference (m : proto.wire.SignalMessage) (before : Slice U8)
    (ctx : prost.encoding.DecodeContext) :
    ∃ decoded after,
      LibSignalReference.Candidate.ProstBytesBuf.PrefixPost before decoded after ∧
      LibSignalReference.Candidate.ProstBytesBuf.ErrorPost before decoded after ∧
      proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
        sliceBuf m 5#u32 .LengthDelimited before ctx =
      (let (status,value,suffix) := LibSignalReference.Candidate.ProstBytes.bytesResult
        (m.pq_ratchet.getD (alloc.vec.Vec.new U8)) decoded after
       ok (status,{m with pq_ratchet := some value},suffix)) := by
  obtain ⟨decoded,after,hp,he,hm⟩ :=
    LibSignalReference.Candidate.ProstBytes.bytes_full_reference
      (toBytesAdapter alloc.vec.VecU8.Insts.ProstEncodingBytesAdapter).sealedBytesAdapterInst
      before (m.pq_ratchet.getD (alloc.vec.Vec.new U8)) ctx
  refine ⟨decoded,after,hp,he,?_⟩
  rw [pq_ratchet_dispatch]
  unfold prost.encoding.bytes.merge
  rw [bytes_slice_adapter,bytes_actual_adapter]
  change (do
    let (status,value,suffix) ← ProstBytesCandidate.encoding.bytes.merge
      (LibSignalReference.Candidate.ProstBytes.withActualReplace
        (toBytesAdapter alloc.vec.VecU8.Insts.ProstEncodingBytesAdapter).sealedBytesAdapterInst)
      LibSignalReference.Candidate.ProstBytesBuf.sliceBuf .LengthDelimited
      (m.pq_ratchet.getD (alloc.vec.Vec.new U8)) before ctx
    ok (status,{m with pq_ratchet := some value},suffix)) = _
  rw [hm]
  cases decoded <;> simp only [bind_tc_ok]
theorem addresses_full_reference (m : proto.wire.SignalMessage) (before : Slice U8)
    (ctx : prost.encoding.DecodeContext) :
    ∃ decoded after,
      LibSignalReference.Candidate.ProstBytesBuf.PrefixPost before decoded after ∧
      LibSignalReference.Candidate.ProstBytesBuf.ErrorPost before decoded after ∧
      proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
        sliceBuf m 6#u32 .LengthDelimited before ctx =
      (let (status,value,suffix) := LibSignalReference.Candidate.ProstBytes.bytesResult
        (m.addresses.getD (alloc.vec.Vec.new U8)) decoded after
       ok (status,{m with addresses := some value},suffix)) := by
  obtain ⟨decoded,after,hp,he,hm⟩ :=
    LibSignalReference.Candidate.ProstBytes.bytes_full_reference
      (toBytesAdapter alloc.vec.VecU8.Insts.ProstEncodingBytesAdapter).sealedBytesAdapterInst
      before (m.addresses.getD (alloc.vec.Vec.new U8)) ctx
  refine ⟨decoded,after,hp,he,?_⟩
  rw [addresses_dispatch]
  unfold prost.encoding.bytes.merge
  rw [bytes_slice_adapter,bytes_actual_adapter]
  change (do
    let (status,value,suffix) ← ProstBytesCandidate.encoding.bytes.merge
      (LibSignalReference.Candidate.ProstBytes.withActualReplace
        (toBytesAdapter alloc.vec.VecU8.Insts.ProstEncodingBytesAdapter).sealedBytesAdapterInst)
      LibSignalReference.Candidate.ProstBytesBuf.sliceBuf .LengthDelimited
      (m.addresses.getD (alloc.vec.Vec.new U8)) before ctx
    ok (status,{m with addresses := some value},suffix)) = _
  rw [hm]
  cases decoded <;> simp only [bind_tc_ok]

#print axioms field_slice_adapter
#print axioms bytes_actual_adapter
#print axioms counter_full_reference
#print axioms ratchet_key_full_reference
#print axioms previous_counter_full_reference
#print axioms ciphertext_full_reference
#print axioms pq_ratchet_full_reference
#print axioms addresses_full_reference
end DispatcherIntegration
