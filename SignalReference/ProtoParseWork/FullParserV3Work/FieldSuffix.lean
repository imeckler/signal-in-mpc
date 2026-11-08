import ProtoParseWork.FullParserV3Work.Suffix
import ProtoParseWork.FullParserV3Work.KnownTotality
open Aeneas Aeneas.Std Result
open SignalMessageIntegration DispatcherIntegration
namespace FullParserV3
set_option maxHeartbeats 1000000

theorem field_decoder_suffix (before after : Slice U8)
    (decoded : core.result.Result U64 ProstFieldCandidate.error.DecodeError)
    (hp : LibSignalReference.Candidate.ProstFieldBuf.PrefixPost before decoded after)
    (he : LibSignalReference.Candidate.ProstFieldBuf.ErrorPost before decoded after) : IsSuffix before after := by
  cases decoded with
  | Ok value => obtain ⟨count,hc,_,_,hr⟩ := hp; exact ⟨count,hc,hr⟩
  | Err error =>
    have hr : after = if LibSignalReference.Candidate.ProstFieldBuf.FastGuard before then before
      else LibSignalReference.Candidate.ProstFieldBuf.drop before (min 10 before.length) := he
    by_cases hf : LibSignalReference.Candidate.ProstFieldBuf.FastGuard before
    · rw [if_pos hf] at hr; rw [hr]; exact suffix_refl _
    · rw [if_neg hf] at hr; exact ⟨min 10 before.length,by omega,hr⟩

theorem bytes_decoder_suffix (before after : Slice U8)
    (decoded : core.result.Result U64 ProstBytesCandidate.error.DecodeError)
    (hp : LibSignalReference.Candidate.ProstBytesBuf.PrefixPost before decoded after)
    (he : LibSignalReference.Candidate.ProstBytesBuf.ErrorPost before decoded after) : IsSuffix before after := by
  cases decoded with
  | Ok value => obtain ⟨count,hc,_,_,hr⟩ := hp; exact ⟨count,hc,hr⟩
  | Err error =>
    have hr : after = if LibSignalReference.Candidate.ProstBytesBuf.FastGuard before then before
      else LibSignalReference.Candidate.ProstBytesBuf.drop before (min 10 before.length) := he
    by_cases hf : LibSignalReference.Candidate.ProstBytesBuf.FastGuard before
    · rw [if_pos hf] at hr; rw [hr]; exact suffix_refl _
    · rw [if_neg hf] at hr; exact ⟨min 10 before.length,by omega,hr⟩

theorem uint32_merge_suffix (wire : prost.encoding.wire_type.WireType)
    (old value : U32) (before after : Slice U8) (ctx : prost.encoding.DecodeContext)
    (status : core.result.Result Unit prost.error.DecodeError)
    (hm : prost.encoding.uint32.merge DispatcherIntegration.sliceBuf wire old before ctx = ok (status,value,after)) :
    IsSuffix before after := by
  by_cases hw : wire = .Varint
  · subst wire
    obtain ⟨decoded,remaining,hp,he,hr⟩ := LibSignalReference.Candidate.ProstField.uint32_full_reference before old ⟨ctx.recurse_count⟩
    have hs := field_decoder_suffix before remaining decoded hp he
    unfold prost.encoding.uint32.merge at hm
    rw [field_slice_adapter] at hm
    simp only [toFieldWire] at hm
    rw [hr] at hm
    cases decoded <;> cases hm <;> exact hs
  · have hw' : toFieldWire wire ≠ .Varint := by cases wire <;> simp_all [toFieldWire]
    unfold prost.encoding.uint32.merge at hm
    rw [LibSignalReference.Candidate.ProstField.uint32_wire_error _ _ _ _ _ hw'] at hm
    cases hm
    exact suffix_refl before

theorem bytes_merge_suffix (wire : prost.encoding.wire_type.WireType)
    (old value : alloc.vec.Vec U8) (before after : Slice U8) (ctx : prost.encoding.DecodeContext)
    (status : core.result.Result Unit prost.error.DecodeError)
    (hm : prost.encoding.bytes.merge alloc.vec.VecU8.Insts.ProstEncodingBytesAdapter
      DispatcherIntegration.sliceBuf wire old before ctx = ok (status,value,after)) : IsSuffix before after := by
  by_cases hw : wire = .LengthDelimited
  · subst wire
    obtain ⟨decoded,remaining,hp,he,hr⟩ := LibSignalReference.Candidate.ProstBytes.bytes_full_reference
      (toBytesAdapter alloc.vec.VecU8.Insts.ProstEncodingBytesAdapter).sealedBytesAdapterInst before old ctx
    have hs := bytes_decoder_suffix before remaining decoded hp he
    unfold prost.encoding.bytes.merge at hm
    rw [bytes_slice_adapter,bytes_actual_adapter] at hm
    simp only [toBytesWire] at hm
    rw [hr] at hm
    cases decoded with
    | Err error => cases hm; exact hs
    | Ok length =>
      dsimp only [LibSignalReference.Candidate.ProstBytes.bytesResult] at hm
      split at hm
      · rename_i hn
        cases hm
        exact suffix_trans hs ⟨length.val,hn,rfl⟩
      · cases hm
        exact hs
  · have hw' : toBytesWire wire ≠ .LengthDelimited := by cases wire <;> simp_all [toBytesWire]
    unfold prost.encoding.bytes.merge at hm
    rw [LibSignalReference.Candidate.ProstBytes.bytes_wire_error _ _ _ _ _ _ hw'] at hm
    cases hm
    exact suffix_refl before

#print axioms uint32_merge_suffix
#print axioms bytes_merge_suffix
end FullParserV3
