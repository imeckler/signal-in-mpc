import ProtoParseWork.KeyReferenceWork.Replayed.SlowReference

namespace LibSignalReference.Candidate.ProstKeyVarint
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal TlsMpc.Signal.VarintDecode
open LibSignalReference.Candidate.ProstKeySlice
set_option maxHeartbeats 300000

def PrefixPost (bytes : Slice U8) (result : core.result.Result U64 ProstKeyCandidate.error.DecodeError)
    (remaining : Slice U8) : Prop :=
  match result with
  | .Ok value => ∃ count, count ≤ bytes.length ∧ count ≤ 10 ∧
      ProtoParse.decodePrefix Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes) 0 =
        ⟨255,BitVec.ofNat 64 count,value.bv⟩ ∧ remaining = drop bytes count
  | .Err error => error = invalidError ∧
      (ProtoParse.decodePrefix Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes) 0).ok = 0

theorem decode_index_bounds (bytes : Slice U8) :
    (Spqr.decode (contents bytes)).index ≤ bytes.length ∧ (Spqr.decode (contents bytes)).index ≤ 10 := by
  have h := (Spqr.run_index_bounds (contents bytes) (min 10 (contents bytes).length) 0 0 false).2
  change (Spqr.decode (contents bytes)).index ≤ 0+min 10 (contents bytes).length at h
  simp only [Nat.zero_add] at h
  have hl : (contents bytes).length = bytes.length := List.length_map _
  rw [hl] at h
  exact ⟨by omega,by omega⟩

theorem prefix_decode_failed (wire : List (BitVec 8)) (h : (Spqr.decode wire).done = false) :
    (ProtoParse.decodePrefix Spqr.concrete Word64.concrete ByteAuth.concrete wire 0).ok = 0 := by
  unfold ProtoParse.decodePrefix
  simp only [List.drop_zero,Spqr.decodeCore_spec,Spqr.encodeResult,h,Bool.false_eq_true,if_false]
  exact BitVec.zero_and

theorem prefix_overflow (wire : List (BitVec 8)) (value : BitVec 64)
    (hs : Spqr.decode wire = ⟨value,10,true⟩) (hb : 2 ≤ (wire[9]?.getD 0).toNat) :
    (ProtoParse.decodePrefix Spqr.concrete Word64.concrete ByteAuth.concrete wire 0).ok = 0 := by
  unfold ProtoParse.decodePrefix
  simp only [List.drop_zero,Spqr.decodeCore_spec,hs,Spqr.encodeResult,if_true,OpenResult.get,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  have heq : ByteAuth.eqMask ByteAuth.concrete (BitVec.ofNat 8 10) (ByteAuth.concrete.const 10) = 255 := by decide
  rw [heq]
  change ByteAuth.concrete.and 255 (Word64.bor ByteAuth.concrete 0
    (ByteAuth.zeroMask ByteAuth.concrete ((wire[9]?.getD 0) &&& 254))) = 0
  rw [ByteAuth.zeroMask_value,if_neg (mask254_large _ hb)]
  rfl

theorem prefix_stop_done (bytes : Slice U8) (h : (Spqr.decode (contents bytes)).done = true) :
    (ProtoParse.decodePrefix Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes) 0).stop =
      BitVec.ofNat 64 (Spqr.decode (contents bytes)).index := by
  have hn : (Spqr.decode (contents bytes)).index < 256 := by have hb := decode_index_bounds bytes; omega
  unfold ProtoParse.decodePrefix
  simp only [List.drop_zero,Spqr.decodeCore_spec,Spqr.encodeResult,h,if_true,OpenResult.get,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,pack_count _ hn]
  exact BitVec.zero_add _

/-- Successful actual slice results carry a bounded count; this derives the
bound from the already proved strict prefix bridge, without changing its proof. -/
theorem slice_count_bound (bytes : Slice U8) (value : U64) (count : Usize)
    (hm : Matches (contents bytes) (.Ok (value,count))) :
    count.val ≤ bytes.length ∧ count.val ≤ 10 := by
  have hd : (Spqr.decode (contents bytes)).done = true := by
    by_contra hn
    have hf : (Spqr.decode (contents bytes)).done = false := Bool.eq_false_iff.mpr hn
    have hz := prefix_decode_failed (contents bytes) hf
    have hp := congrArg ProtoParse.Decoded.ok hm
    rw [hz] at hp
    change (0 : BitVec 8) = 255 at hp
    contradiction
  have hc := congrArg ProtoParse.Decoded.stop hm
  rw [prefix_stop_done bytes hd] at hc
  have hv := congrArg BitVec.toNat hc
  have hn64 : count.val < 2^64 := by
    have hb := count.hmax
    have hm := System.Platform.numBits_eq
    simp only [UScalarTy.Usize_numBits_eq] at hb
    rcases hm with hm | hm <;> rw [hm] at hb <;> omega
  have bounds := decode_index_bounds bytes
  have hi64 : (Spqr.decode (contents bytes)).index < 2^64 := by omega
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn64,Nat.mod_eq_of_lt hi64] at hv
  omega

theorem stateResult_post (bytes : Slice U8) :
    PrefixPost bytes (stateResult bytes (Spqr.decode (contents bytes)))
      (drop bytes (Spqr.decode (contents bytes)).index) := by
  have bounds := decode_index_bounds bytes
  generalize hs : Spqr.decode (contents bytes) = state at *
  rcases state with ⟨value,index,done⟩
  cases done with
  | false =>
      refine ⟨rfl,?_⟩
      apply prefix_decode_failed
      rw [hs]
  | true =>
      by_cases hover : index = 10 ∧ 2 ≤ (byte bytes 9).val
      · rcases hover with ⟨hi,hb⟩
        subst index
        have he : stateResult bytes ⟨value,10,true⟩ = .Err invalidError := by
          simp only [stateResult,if_true,true_and,if_pos hb]
        rw [he]
        change invalidError = invalidError ∧ _
        refine ⟨rfl,prefix_overflow (contents bytes) value hs ?_⟩
        rw [contents_get]
        exact hb
      · simp only [stateResult,if_true,if_neg hover,PrefixPost]
        refine ⟨index,bounds.1,bounds.2,?_,rfl⟩
        apply prefix_accepted (contents bytes) index value hs bounds.2
        intro hi
        rw [contents_get]
        have hn : ¬ 2 ≤ (byte bytes 9).val := fun hb => hover ⟨hi,hb⟩
        change (byte bytes 9).val < 2
        omega

theorem slow_post (bytes : Slice U8) :
    ∃ result remaining,
      ProstKeyCandidate.encoding.varint.decode_varint_slow sliceBuf bytes = .ok (result,remaining) ∧
      PrefixPost bytes result remaining := by
  exact ⟨_,_,slow_reference bytes,stateResult_post bytes⟩

#print axioms slice_count_bound
#print axioms stateResult_post
#print axioms slow_post
end LibSignalReference.Candidate.ProstKeyVarint
