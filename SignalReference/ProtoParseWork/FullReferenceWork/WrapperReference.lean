import ProtoParseWork.FullReferenceWork.StateBridge

namespace LibSignalReference.Candidate.ProstFull
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal TlsMpc.Signal.VarintDecode
open LibSignalReference.Candidate.ProstFullSlice
set_option maxHeartbeats 400000
set_option maxRecDepth 4096

/-- The unchanged wrapper's exact `?`/advance continuation, factored only for proof. -/
def finishSlice (bytes : Slice U8)
    (r : core.result.Result (U64 × Usize) ProstParserFullCandidate.error.DecodeError) :
    Result ((core.result.Result U64 ProstParserFullCandidate.error.DecodeError) × Slice U8) := do
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (value,count) := val
    let next ← sliceBuf.advance bytes count
    .ok (.Ok value,next)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let result ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      U64 (core.convert.FromSame ProstParserFullCandidate.error.DecodeError) residual
    .ok (result,bytes)

theorem fast_post (bytes : Slice U8) (hp : Preconditions bytes) :
    ∃ result remaining,
      (do let r ← ProstParserFullCandidate.encoding.varint.decode_varint_slice bytes
          finishSlice bytes r) = .ok (result,remaining) ∧ PrefixPost bytes result remaining := by
  obtain ⟨r,hr,hm⟩ := decode_reference bytes hp
  rw [hr]
  simp only [bind_tc_ok]
  cases r with
  | Ok pair =>
      rcases pair with ⟨value,count⟩
      have hb := slice_count_bound bytes value count hm
      refine ⟨.Ok value,drop bytes count.val,?_,count.val,hb.1,hb.2,hm,rfl⟩
      change (do let next ← sliceBuf.advance bytes count; Result.ok (core.result.Result.Ok value,next)) = _
      rw [advance_spec bytes count hb.1]
      rfl
  | Err error =>
      exact ⟨.Err error,bytes,rfl,hm⟩

theorem first_post (bytes : Slice U8) (hn : 0 < bytes.length)
    (hb : (byte bytes 0).val < 128) :
    PrefixPost bytes (.Ok (core.convert.num.FromU64U8.from (byte bytes 0))) (drop bytes 1) := by
  refine ⟨1,hn,by decide,?_,rfl⟩
  have hl : 0 < (contents bytes).length := by simpa only [contents,List.length_map] using hn
  have hg : (contents bytes)[0] = (byte bytes 0).bv := by
    have h := contents_get bytes 0
    simpa only [List.getElem?_eq_getElem hl,Option.getD_some] using h
  have hs := prefix_one (contents bytes) hl (by rw [hg]; exact hb)
  rw [hg] at hs
  exact hs

/-- Actual top-level Prost decoder on a contiguous byte slice, for every slice.
No fast-path precondition is imposed on the caller: the Rust dispatch establishes it. -/
theorem decode_reference (bytes : Slice U8) :
    ∃ result remaining,
      ProstParserFullCandidate.encoding.varint.decode_varint sliceBuf bytes = .ok (result,remaining) ∧
      PrefixPost bytes result remaining := by
  rw [ProstParserFullCandidate.encoding.varint.decode_varint,chunk_spec]
  simp only [bind_tc_ok]
  by_cases hz : bytes.len = 0#usize
  · rw [if_pos hz,invalid_conversion]
    refine ⟨.Err invalidError,bytes,rfl,rfl,?_⟩
    apply prefix_decode_failed
    have hl : bytes.length = 0 := by scalar_tac
    have hc : (contents bytes).length = 0 := by simpa only [contents,List.length_map] using hl
    simp only [Spqr.decode,hc,Nat.min_zero,Spqr.run]
  · rw [if_neg hz]
    have hn : 0 < bytes.length := by scalar_tac
    obtain ⟨first,hg,he⟩ := WP.spec_imp_exists (Slice.index_usize_spec bytes 0#usize hn)
    have heq : first = byte bytes 0 := by rw [he,byte_at bytes 0 hn]; rfl
    rw [hg]
    simp only [bind_tc_ok]
    by_cases ht : first < 128#u8
    · rw [if_pos ht,advance_spec bytes 1#usize (by scalar_tac)]
      refine ⟨.Ok (core.convert.num.FromU64U8.from first),drop bytes 1,rfl,?_⟩
      rw [heq]
      exact first_post bytes hn (by rw [← heq]; exact ht)
    · rw [if_neg ht]
      by_cases hl : bytes.len > 10#usize
      · rw [if_pos hl]
        exact fast_post bytes ⟨hn,Or.inl hl⟩
      · rw [if_neg hl]
        obtain ⟨lastIndex,hs,hv⟩ := WP.spec_imp_exists
          (Usize.sub_spec (x := bytes.len) (y := 1#usize) (by scalar_tac))
        have hi : lastIndex.val < bytes.val.length := by scalar_tac
        obtain ⟨last,hg,he⟩ := WP.spec_imp_exists (Slice.index_usize_spec bytes lastIndex hi)
        rw [hs]
        simp only [bind_tc_ok]
        rw [hg]
        simp only [bind_tc_ok]
        by_cases hlast : last < 128#u8
        · rw [if_pos hlast]
          apply fast_post bytes
          refine ⟨hn,Or.inr ?_⟩
          intro i hi heq
          have hie : i = lastIndex.val := by scalar_tac
          subst i
          rw [← he]
          exact hlast
        · rw [if_neg hlast]
          exact slow_post bytes

#print axioms finishSlice
#print axioms fast_post
#print axioms first_post
#print axioms decode_reference
end LibSignalReference.Candidate.ProstFull
