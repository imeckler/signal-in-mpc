import SkipTranslatorWork.Replayed.ArtifactBridge

namespace LibSignalReference.Candidate.ProstSkipBuf
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal TlsMpc.Signal.VarintDecode
open LibSignalReference.Candidate.ProstSkipSlice
set_option maxHeartbeats 400000
set_option maxRecDepth 4096

def FastGuard (bytes : Slice U8) : Prop :=
  10 < bytes.length ∨ (byte bytes (bytes.length-1)).val < 128
instance (bytes : Slice U8) : Decidable (FastGuard bytes) := inferInstanceAs (Decidable (_ ∨ _))

/-- Fast-path errors preserve Buf. The short/chunk slow path consumes all
available bytes on error. This matches actual mutable &[u8] behavior. -/
def ErrorPost (bytes : Slice U8)
    (result : core.result.Result U64 LoopSupportSkip.error.DecodeError)
    (remaining : Slice U8) : Prop :=
  match result with
  | .Ok _ => True
  | .Err _ => remaining = if FastGuard bytes then bytes else drop bytes (min 10 bytes.length)

theorem run_not_done (wire : List (BitVec 8)) (fuel index : Nat) (value : BitVec 64) (done : Bool)
    (h : (Spqr.run wire fuel index value done).done = false) :
    (Spqr.run wire fuel index value done).index = index+fuel := by
  induction fuel generalizing index value done with
  | zero => rfl
  | succ fuel ih =>
      cases done with
      | true => simp only [Spqr.run,if_true] at h; contradiction
      | false =>
          simp only [Spqr.run,Bool.false_eq_true,if_false] at h ⊢
          rw [ih _ _ _ h]
          omega

theorem slow_error_post (bytes : Slice U8) (hguard : ¬FastGuard bytes) :
    ErrorPost bytes (stateResult bytes (Spqr.decode (contents bytes)))
      (drop bytes (Spqr.decode (contents bytes)).index) := by
  have hn : bytes.length ≤ 10 := by have h := hguard; unfold FastGuard at h; omega
  have bounds := decode_index_bounds bytes
  by_cases hd : (Spqr.decode (contents bytes)).done = true
  · by_cases hov : (Spqr.decode (contents bytes)).index = 10 ∧ 2 ≤ (byte bytes 9).val
    · have hlen : bytes.length = 10 := by omega
      simp only [stateResult,hd,if_true,hov.1,true_and,if_pos hov.2,ErrorPost,if_neg hguard,hlen,Nat.min_self]
    · simp only [stateResult,hd,if_true,if_neg hov,ErrorPost]
  · have hf : (Spqr.decode (contents bytes)).done = false := Bool.eq_false_iff.mpr hd
    have hi := run_not_done (contents bytes) (min 10 (contents bytes).length) 0 0 false hf
    have hl : (contents bytes).length = bytes.length := List.length_map _
    change (Spqr.decode (contents bytes)).index = 0+min 10 (contents bytes).length at hi
    rw [Nat.zero_add,hl] at hi
    simp only [stateResult,hf,Bool.false_eq_true,if_false,ErrorPost,if_neg hguard,hi]

theorem fast_error_post (bytes : Slice U8) (hp : Preconditions bytes) (hguard : FastGuard bytes) :
    ∃ result remaining,
      (do let r ← LoopSupportSkip.encoding.varint.decode_varint_slice bytes
          finishSlice bytes r) = .ok (result,remaining) ∧ ErrorPost bytes result remaining := by
  obtain ⟨r,hr,hm⟩ := ProstSkipSlice.decode_reference bytes hp
  rw [hr]
  simp only [bind_tc_ok]
  cases r with
  | Ok pair =>
      rcases pair with ⟨value,count⟩
      have hb := slice_count_bound bytes value count hm
      refine ⟨.Ok value,drop bytes count.val,?_,True.intro⟩
      change (do let next ← sliceBuf.advance bytes count; Result.ok (core.result.Result.Ok value,next)) = _
      rw [advance_spec bytes count hb.1]
      rfl
  | Err error =>
      refine ⟨.Err error,bytes,rfl,?_⟩
      exact (if_pos hguard).symm

/-- Exact failure-side mutation of the unchanged actual full decoder. -/
theorem decode_error_post (bytes : Slice U8) :
    ∃ result remaining,
      LoopSupportSkip.encoding.varint.decode_varint sliceBuf bytes = .ok (result,remaining) ∧
      ErrorPost bytes result remaining := by
  rw [LoopSupportSkip.encoding.varint.decode_varint,chunk_spec]
  simp only [bind_tc_ok]
  by_cases hz : bytes.len = 0#usize
  · rw [if_pos hz,invalid_conversion]
    refine ⟨.Err invalidError,bytes,rfl,?_⟩
    have hl : bytes.length = 0 := by scalar_tac
    have hd : drop bytes 0 = bytes := by apply Subtype.ext; exact List.drop_zero
    change bytes = if FastGuard bytes then bytes else drop bytes (min 10 bytes.length)
    simp only [hl,Nat.min_zero,hd,ite_self]
  · rw [if_neg hz]
    have hn : 0 < bytes.length := by scalar_tac
    obtain ⟨first,hg,he⟩ := WP.spec_imp_exists (Slice.index_usize_spec bytes 0#usize hn)
    rw [hg]
    simp only [bind_tc_ok]
    by_cases ht : first < 128#u8
    · rw [if_pos ht,advance_spec bytes 1#usize (by scalar_tac)]
      exact ⟨.Ok (core.convert.num.FromU64U8.from first),drop bytes 1,rfl,True.intro⟩
    · rw [if_neg ht]
      by_cases hl : bytes.len > 10#usize
      · rw [if_pos hl]
        exact fast_error_post bytes ⟨hn,Or.inl hl⟩ (Or.inl hl)
      · rw [if_neg hl]
        obtain ⟨lastIndex,hs,hv⟩ := WP.spec_imp_exists
          (Usize.sub_spec (x := bytes.len) (y := 1#usize) (by scalar_tac))
        have hi : lastIndex.val < bytes.val.length := by scalar_tac
        obtain ⟨last,hg,he⟩ := WP.spec_imp_exists (Slice.index_usize_spec bytes lastIndex hi)
        have heq : last = byte bytes (bytes.length-1) := by
          have hiq : lastIndex.val = bytes.length-1 := by scalar_tac
          rw [byte_at bytes (bytes.length-1) (by omega)]
          simpa only [hiq] using he
        rw [hs]
        simp only [bind_tc_ok]
        rw [hg]
        simp only [bind_tc_ok]
        by_cases hlast : last < 128#u8
        · rw [if_pos hlast]
          have hp : Preconditions bytes := by
            refine ⟨hn,Or.inr ?_⟩
            intro i hi heqi
            have hie : i = lastIndex.val := by scalar_tac
            subst i
            rw [← he]
            exact hlast
          exact fast_error_post bytes hp (Or.inr (by rw [← heq]; exact hlast))
        · rw [if_neg hlast]
          refine ⟨_,_,slow_reference bytes,slow_error_post bytes ?_⟩
          rintro (hlong | hsmall)
          · exact hl hlong
          · exact hlast (by rw [heq]; exact hsmall)

theorem decode_full_reference (bytes : Slice U8) :
    ∃ result remaining,
      LoopSupportSkip.encoding.varint.decode_varint sliceBuf bytes = .ok (result,remaining) ∧
      PrefixPost bytes result remaining ∧ ErrorPost bytes result remaining := by
  obtain ⟨result,remaining,hd,hp⟩ := decode_reference bytes
  obtain ⟨result',remaining',hd',he⟩ := decode_error_post bytes
  rw [hd] at hd'
  cases hd'
  exact ⟨result,remaining,hd,hp,he⟩

#print axioms run_not_done
#print axioms slow_error_post
#print axioms fast_error_post
#print axioms decode_error_post
#print axioms decode_full_reference
end LibSignalReference.Candidate.ProstSkipBuf
