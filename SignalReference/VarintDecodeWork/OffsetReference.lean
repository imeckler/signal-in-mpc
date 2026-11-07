import VarintDecodeWork.Bridge

namespace LibSignalReference.Candidate.VarintDecode
open Aeneas Aeneas.Std TlsMpc
open TlsMpc.Signal.VarintDecode

set_option maxHeartbeats 2000000

/-- Actual index arithmetic and reads agree after removing a prefix. The
checked addition is justified by the real slice bound, not wraparound. -/
theorem loop_body_suffix (bytes : Slice U8) (start i maxIndex : Usize)
    (hbound : start.val + maxIndex.val ≤ bytes.length) (value : U64) (done : Bool) :
    _root_.SpqrVarintDecode.decode_varint_loop.body bytes start maxIndex value i done =
      _root_.SpqrVarintDecode.decode_varint_loop.body (bytes.drop start) 0#usize maxIndex value i done := by
  by_cases hi : i < maxIndex
  · cases done with
    | true => simp [_root_.SpqrVarintDecode.decode_varint_loop.body, hi]
    | false =>
        have hiv : i.val < maxIndex.val := hi
        obtain ⟨pos, hpos, hposv⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := start) (y := i) (by scalar_tac))
        have hread : Slice.index_usize bytes pos = Slice.index_usize (bytes.drop start) i := by
          simp only [Slice.index_usize, Slice.getElem?_Usize_eq, Slice.drop,
            List.getElem?_drop, hposv]
        with_unfolding_all simp only [_root_.SpqrVarintDecode.decode_varint_loop.body,
          if_pos hi, Bool.false_eq_true, if_false, hpos, zero_add, bind_tc_ok, hread]
  · simp [_root_.SpqrVarintDecode.decode_varint_loop.body, hi]

/-- Bisimulation of the unchanged actual loop at original and suffix offsets. -/
theorem loop_suffix (bytes : Slice U8) (start maxIndex i : Usize)
    (hi : i.val ≤ maxIndex.val) (hm : maxIndex.val ≤ 10)
    (hbound : start.val + maxIndex.val ≤ bytes.length) (value : U64) (done : Bool) :
    _root_.SpqrVarintDecode.decode_varint_loop bytes start value i done maxIndex =
      _root_.SpqrVarintDecode.decode_varint_loop (bytes.drop start) 0#usize value i done maxIndex := by
  have hsuffix : maxIndex.val ≤ (bytes.drop start).length := by
    simp only [Slice.length, Slice.drop, List.length_drop]
    change start.val + maxIndex.val ≤ bytes.val.length at hbound
    omega
  generalize hf : maxIndex.val - i.val = fuel
  induction fuel generalizing i value done with
  | zero =>
      have hge : ¬ i < maxIndex := by change ¬i.val < maxIndex.val; omega
      conv_lhs => unfold _root_.SpqrVarintDecode.decode_varint_loop; rw [loop]
      conv_rhs => unfold _root_.SpqrVarintDecode.decode_varint_loop; rw [loop]
      simp [_root_.SpqrVarintDecode.decode_varint_loop.body, hge]
  | succ fuel ih =>
      have hit : i.val < maxIndex.val := by omega
      have hlt : i < maxIndex := hit
      cases done with
      | true =>
          conv_lhs => unfold _root_.SpqrVarintDecode.decode_varint_loop; rw [loop]
          conv_rhs => unfold _root_.SpqrVarintDecode.decode_varint_loop; rw [loop]
          simp [_root_.SpqrVarintDecode.decode_varint_loop.body, hlt]
      | false =>
          obtain ⟨nextIndex, hbody, hnext⟩ :=
            loop_body_continue (bytes.drop start) i maxIndex hit hm hsuffix value
          conv_lhs => unfold _root_.SpqrVarintDecode.decode_varint_loop; rw [loop]
          conv_rhs => unfold _root_.SpqrVarintDecode.decode_varint_loop; rw [loop]
          dsimp only
          rw [loop_body_suffix bytes start i maxIndex hbound value false, hbody]
          simp only
          exact ih nextIndex (by omega) _ _ (by omega)

def MatchesAt (start : Usize) (state : Spqr.State)
    (result : core.result.Result U64 _root_.SpqrVarintDecode.Error) (cursor : Usize) : Prop :=
  if state.done then result = .Ok ⟨state.value⟩ ∧ cursor.val = start.val + state.index
  else result = .Err .MsgDecode ∧ cursor = start

/-- The exact unchanged decoder at every starting Usize, including starts at
or beyond the end. Every reported failure preserves the original offset. -/
theorem decode_at_reference (bytes : Slice U8) (start : Usize) :
    ∃ result cursor,
      _root_.SpqrVarintDecode.decode_varint bytes start = .ok (result, cursor) ∧
      MatchesAt start (Spqr.decode (contents (bytes.drop start))) result cursor := by
  by_cases hout : start ≥ Slice.len bytes
  · refine ⟨.Err .MsgDecode, start, ?_, ?_⟩
    · simp only [_root_.SpqrVarintDecode.decode_varint, if_pos hout]
    · have hlen : bytes.length ≤ start.val := hout
      have hempty : contents (bytes.drop start) = [] := by
        simp [contents, Slice.drop, List.drop_eq_nil_of_le hlen]
      simp [hempty, MatchesAt, Spqr.decode, Spqr.run]
  · have hstart : start.val < bytes.length := by change ¬start.val ≥ bytes.length at hout; omega
    obtain ⟨remaining, hremaining, hremainingv⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := Slice.len bytes) (y := start) (by scalar_tac))
    have hrem : remaining.val = bytes.length - start.val := by simpa using hremainingv.1
    let maxIndex := core.cmp.impls.OrdUsize.min 10#usize remaining
    have hm : maxIndex.val = min 10 (bytes.length - start.val) := by simp [maxIndex, hrem]
    have hsuffix : (bytes.drop start).length = bytes.length - start.val := by simp [Slice.drop]
    obtain ⟨⟨value, relative, done⟩, hloop, hstate⟩ := loop_reference (bytes.drop start) maxIndex 0#usize
      (by scalar_tac) (by omega) (by omega) 0#u64 false
    have heq := loop_suffix bytes start maxIndex 0#usize (by scalar_tac) (by omega) (by omega) 0#u64 false
    have hs : loopState (value, relative, done) = Spqr.decode (contents (bytes.drop start)) := by
      simpa [Spqr.decode, contents, hm, Slice.drop, Slice.length] using hstate
    have hrelative : relative.val ≤ maxIndex.val := by
      have hstate' : loopState (value, relative, done) =
          Spqr.run (contents (bytes.drop start)) maxIndex.val 0 0 false := by simpa using hstate
      have hp := congrArg Spqr.State.index hstate'
      have hb := (Spqr.run_index_bounds (contents (bytes.drop start)) maxIndex.val 0 0 false).2
      simp only [loopState] at hp
      omega
    obtain ⟨cursor, hcursor, hcursorv⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := start) (y := relative) (by scalar_tac))
    have hmin : core.cmp.min core.cmp.OrdUsize _root_.SpqrVarintDecode.MAX_VARINT_BYTES_LEN
        remaining = .ok maxIndex := by with_unfolding_all rfl
    have hd : _root_.SpqrVarintDecode.decode_varint bytes start =
        if done then .ok (.Ok value, cursor) else .ok (.Err .MsgDecode, start) := by
      unfold _root_.SpqrVarintDecode.decode_varint
      with_unfolding_all simp only [if_neg hout, hremaining, bind_tc_ok, hmin, heq, hloop]
      cases done <;> simp [hcursor]
    cases done with
    | false =>
        refine ⟨.Err .MsgDecode, start, hd, ?_⟩
        rw [← hs]
        exact ⟨rfl, rfl⟩
    | true =>
        refine ⟨.Ok value, cursor, hd, ?_⟩
        rw [← hs]
        exact ⟨rfl, hcursorv⟩

/-- Direct translation-equivariance statement, retaining the actual Result
and checked cursor update. No decoding model replaces either Rust operation. -/
theorem decode_suffix (bytes : Slice U8) (start : Usize) :
    _root_.SpqrVarintDecode.decode_varint bytes start = (do
      let (result, consumed) ← _root_.SpqrVarintDecode.decode_varint (bytes.drop start) 0#usize
      match result with
      | .Ok value =>
          let cursor ← start + consumed
          .ok (.Ok value, cursor)
      | .Err error => .ok (.Err error, start)) := by
  obtain ⟨result, cursor, hd, hm⟩ := decode_at_reference bytes start
  obtain ⟨prefixResult, consumed, hp, hpm⟩ := decode_reference (bytes.drop start)
  rw [hd, hp]
  simp only [bind_tc_ok]
  unfold MatchesAt at hm
  unfold Matches at hpm
  split at hm
  · rename_i done
    simp only [done, if_true] at hpm
    rcases hm with ⟨rfl, hcursor⟩
    rcases hpm with ⟨rfl, hconsumed⟩
    have hbound : start.val + consumed.val ≤ Usize.max := by scalar_tac
    obtain ⟨updated, hu, hv⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := start) (y := consumed) hbound)
    have he : updated = cursor := by scalar_tac
    simp [hu, he]
  · rename_i done
    simp only [done] at hpm
    rcases hm with ⟨rfl, rfl⟩
    rcases hpm with ⟨rfl, rfl⟩
    rfl

end LibSignalReference.Candidate.VarintDecode
