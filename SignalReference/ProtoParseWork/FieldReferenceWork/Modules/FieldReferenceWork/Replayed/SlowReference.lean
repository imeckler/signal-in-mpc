import FieldReferenceWork.Replayed.SliceAdapter

namespace LibSignalReference.Candidate.ProstFieldBuf
open Aeneas Aeneas.Std TlsMpc.Signal.VarintDecode
open LibSignalReference.Candidate.ProstFieldSlice
set_option maxHeartbeats 500000
set_option maxRecDepth 4096

def stateResult (bytes : Slice U8) (state : Spqr.State) :
    core.result.Result U64 ProstFieldCandidate.error.DecodeError :=
  if state.done then
    if state.index = 10 ∧ 2 ≤ (byte bytes 9).val then .Err invalidError else .Ok ⟨state.value⟩
  else .Err invalidError

theorem stateResult_done (bytes : Slice U8) (i : Nat) (value : BitVec 64) :
    stateResult bytes ⟨value,i+1,true⟩ =
      if i = 9 then
        if 2 ≤ (byte bytes i).val then .Err invalidError else .Ok ⟨value⟩
      else .Ok ⟨value⟩ := by
  by_cases hi : i = 9
  · subst i; simp only [stateResult,if_true,true_and]
  · have hn : i+1 ≠ 10 := by omega
    simp only [stateResult,if_true,hn,false_and,if_false,hi]

theorem invalid_conversion :
    core.convert.IntoFrom.into
      ProstFieldCandidate.error.DecodeError.Insts.CoreConvertFromDecodeErrorKind
      ProstFieldCandidate.error.DecodeErrorKind.InvalidVarint = .ok invalidError := rfl

theorem getByte_drop (bytes : Slice U8) (i : Nat) (hi : i < bytes.length) :
    sliceBuf.get_u8 (drop bytes i) = .ok (byte bytes i,drop bytes (i+1)) := by
  have hn : 0 < (drop bytes i).length := by rw [drop_length]; omega
  rw [getByte_spec _ hn,drop_add]
  congr 2
  rw [byte_at bytes i hi]
  exact List.getElem_drop

theorem slow_payload (b : U8) (count : Usize) (hc : count.val < 10) :
    (do let amount ← count * 7#usize
        core.convert.num.FromU64U8.from (b &&& 127#u8) <<< amount) =
      .ok (⟨Spqr.payload b.bv count.val⟩ : U64) := by
  obtain ⟨amount,ha,hv⟩ := WP.spec_imp_exists
    (Usize.mul_spec (x := count) (y := 7#usize) (by scalar_tac))
  rw [ha]
  simp only [bind_tc_ok]
  have hamount : amount.val = 7*count.val := by scalar_tac
  have hshift : amount.val < UScalarTy.U64.numBits := by change amount.val < 64; omega
  change UScalar.shiftLeft_UScalar _ amount = _
  unfold UScalar.shiftLeft_UScalar UScalar.shiftLeft
  rw [if_pos hshift]
  simp only [hamount]
  change Result.ok (⟨((b.bv &&& 127).setWidth 64) <<< (7*count.val)⟩ : U64) =
    Result.ok ⟨((b.bv.setWidth 64) &&& 127) <<< (7*count.val)⟩
  rw [BitVec.setWidth_and]
  rfl

theorem body_some (bytes : Slice U8) (iter : core.ops.range.Range Usize) (value : U64)
    (hi : iter.start.val < iter.end.val) (he : iter.end.val ≤ 10) (hl : iter.end.val ≤ bytes.length) :
    ∃ nextIter,
      nextIter.start.val = iter.start.val+1 ∧ nextIter.end = iter.end ∧
      ProstFieldCandidate.encoding.varint.decode_varint_slow_loop.body sliceBuf iter
        (drop bytes iter.start.val) value =
      .ok (if (byte bytes iter.start.val).val < 128 then
        .done (stateResult bytes ⟨value.bv ||| Spqr.payload (byte bytes iter.start.val).bv iter.start.val,
          iter.start.val+1,true⟩,drop bytes (iter.start.val+1))
      else .cont (nextIter,drop bytes (iter.start.val+1),
        (⟨value.bv ||| Spqr.payload (byte bytes iter.start.val).bv iter.start.val⟩ : U64))) := by
  obtain ⟨⟨opt,nextIter⟩,hn,ho,hs,hei⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_Usize_some_spec iter hi)
  refine ⟨nextIter,hs,hei,?_⟩
  rw [ho] at hn
  have hg := getByte_drop bytes iter.start.val (by omega)
  have hp := slow_payload (byte bytes iter.start.val) iter.start (by omega)
  have ht : (byte bytes iter.start.val ≤ 127#u8) ↔ (byte bytes iter.start.val).val < 128 := by
    change (byte bytes iter.start.val).val ≤ 127 ↔ _
    omega
  have h9 : iter.start = 9#usize ↔ iter.start.val = 9 := by
    constructor
    · intro h; rw [h]; rfl
    · intro h; exact UScalar.eq_of_val_eq h
  unfold ProstFieldCandidate.encoding.varint.decode_varint_slow_loop.body
  rw [hn]
  simp only [bind_tc_ok,hg,lift]
  change (Bind.bind (iter.start * 7#usize) (fun amount =>
    Bind.bind (core.convert.num.FromU64U8.from (byte bytes iter.start.val &&& 127#u8) <<< amount) _)) = _
  rw [← bind_assoc_eq,hp]
  have hb2 : (byte bytes iter.start.val ≥ 2#u8) ↔ 2 ≤ (byte bytes iter.start.val).val := Iff.rfl
  simp only [bind_tc_ok,ht,h9,hb2,invalid_conversion,stateResult_done]
  split_ifs <;> rfl

theorem body_none (iter : core.ops.range.Range Usize) (buf : Slice U8) (value : U64)
    (hi : iter.end.val ≤ iter.start.val) :
    ProstFieldCandidate.encoding.varint.decode_varint_slow_loop.body sliceBuf iter buf value =
      .ok (.done (.Err invalidError,buf)) := by
  obtain ⟨⟨opt,nextIter⟩,hn,ho,hi'⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_Usize_none_spec iter hi)
  rw [ho] at hn
  unfold ProstFieldCandidate.encoding.varint.decode_varint_slow_loop.body
  rw [hn]
  simp only [bind_tc_ok,invalid_conversion]
  rfl

/-- Complete actual slow loop: exact strict result and exact consumed suffix.
The remaining public fuel bounds every get_u8, multiplication and u64 shift. -/
theorem slow_loop_reference (bytes : Slice U8) (iter : core.ops.range.Range Usize) (value : U64)
    (hi : iter.start.val ≤ iter.end.val) (he : iter.end.val ≤ 10) (hl : iter.end.val ≤ bytes.length) :
    ProstFieldCandidate.encoding.varint.decode_varint_slow_loop sliceBuf iter
      (drop bytes iter.start.val) value =
      let state := Spqr.run (contents bytes) (iter.end.val-iter.start.val) iter.start.val value.bv false
      .ok (stateResult bytes state,drop bytes state.index) := by
  generalize hf : iter.end.val-iter.start.val = fuel
  induction fuel generalizing iter value with
  | zero =>
      have hge : iter.end.val ≤ iter.start.val := by omega
      unfold ProstFieldCandidate.encoding.varint.decode_varint_slow_loop
      rw [loop]
      dsimp only
      rw [body_none iter _ value hge]
      rfl
  | succ fuel ih =>
      have hit : iter.start.val < iter.end.val := by omega
      obtain ⟨nextIter,hs,hei,hbody⟩ := body_some bytes iter value hit he hl
      unfold ProstFieldCandidate.encoding.varint.decode_varint_slow_loop
      rw [loop]
      dsimp only
      rw [hbody]
      by_cases hb : (byte bytes iter.start.val).val < 128
      · simp only [if_pos hb]
        simp only [Spqr.run,Bool.false_eq_true,if_false,contents_get,
          terminates_of_small _ hb,run_done]
      · have hlarge : 128 ≤ (byte bytes iter.start.val).val := by omega
        simp only [if_neg hb]
        simp only [Spqr.run,Bool.false_eq_true,if_false,contents_get,
          terminates_of_large _ hlarge]
        have ht := ih nextIter
          (⟨value.bv ||| Spqr.payload (byte bytes iter.start.val).bv iter.start.val⟩ : U64)
          (by rw [hs,hei]; omega) (by rw [hei]; exact he) (by rw [hei]; exact hl)
          (by rw [hs,hei]; omega)
        simpa only [ProstFieldCandidate.encoding.varint.decode_varint_slow_loop,hs] using ht

/-- Entire actual slow decoder for arbitrary contiguous byte slices, including
empty/truncated and overflowing encodings. Error consumption is preserved. -/
theorem slow_reference (bytes : Slice U8) :
    ProstFieldCandidate.encoding.varint.decode_varint_slow sliceBuf bytes =
      let state := Spqr.decode (contents bytes)
      .ok (stateResult bytes state,drop bytes state.index) := by
  let bound := core.cmp.impls.OrdUsize.min 10#usize bytes.len
  have hm : bound.val = min 10 bytes.length := by simp [bound]
  have hmin : core.cmp.min core.cmp.OrdUsize 10#usize bytes.len = .ok bound := by with_unfolding_all rfl
  have hr := slow_loop_reference bytes ⟨0#usize,bound⟩ 0#u64 (by scalar_tac)
    (by change bound.val ≤ 10; rw [hm]; exact Nat.min_le_left _ _)
    (by change bound.val ≤ bytes.length; rw [hm]; exact Nat.min_le_right _ _)
  have hz : (0#usize).val = 0 := rfl
  have hvz : (0#u64).bv = 0 := rfl
  have hd : drop bytes 0 = bytes := by apply Subtype.ext; exact List.drop_zero
  unfold ProstFieldCandidate.encoding.varint.decode_varint_slow
  rw [remaining_spec]
  simp only [bind_tc_ok]
  rw [hmin]
  simp only [bind_tc_ok]
  simpa only [hz,hvz,hd,hm,Spqr.decode,contents,List.length_map,Slice.length,Nat.sub_zero] using hr

#print axioms slow_loop_reference
#print axioms slow_reference
#print axioms body_some
#print axioms body_none
end LibSignalReference.Candidate.ProstFieldBuf
