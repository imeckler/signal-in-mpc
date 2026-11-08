import ProtoParseWork.FullParserV3Work.SkipTotality
open Aeneas Aeneas.Std Result
open LoopSupportSkip
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkip
open LibSignalReference.Candidate.ProstSkipKey
namespace FullParserV3
set_option maxHeartbeats 1000000

def IsSuffix (before after : Slice U8) : Prop :=
  ∃ used, used ≤ before.length ∧ after = drop before used

theorem suffix_refl (before : Slice U8) : IsSuffix before before := by
  refine ⟨0,Nat.zero_le _,?_⟩
  apply Subtype.ext
  simp [drop]

theorem suffix_trans {before middle after : Slice U8}
    (h1 : IsSuffix before middle) (h2 : IsSuffix middle after) : IsSuffix before after := by
  obtain ⟨n,hn,hm⟩ := h1
  obtain ⟨m,hmb,ha⟩ := h2
  refine ⟨n+m,?_,?_⟩
  · rw [hm,drop_length] at hmb; omega
  · rw [ha,hm,drop_add]

theorem varint_suffix (before after : Slice U8)
    (result : core.result.Result U64 error.DecodeError)
    (hd : encoding.varint.decode_varint sliceBuf before = ok (result,after)) : IsSuffix before after := by
  obtain ⟨r,remaining,hr,hp,he⟩ := decode_full_reference before
  rw [hd] at hr
  cases hr
  cases result with
  | Ok value => obtain ⟨count,hc,_,_,hrest⟩ := hp; exact ⟨count,hc,hrest⟩
  | Err e =>
    have hrest : after = if FastGuard before then before else drop before (min 10 before.length) := he
    by_cases hf : FastGuard before
    · rw [if_pos hf] at hrest; rw [hrest]; exact suffix_refl before
    · rw [if_neg hf] at hrest; exact ⟨min 10 before.length,by omega,hrest⟩

theorem key_suffix (before after : Slice U8)
    (result : core.result.Result (U32 × encoding.wire_type.WireType) error.DecodeError)
    (hd : encoding.decode_key sliceBuf before = ok (result,after)) : IsSuffix before after := by
  obtain ⟨r,remaining,hv,hp,he,hk⟩ := decode_key_reference before
  rw [hd] at hk
  have ha : after = remaining := congrArg Prod.snd (Result.ok.inj hk)
  rw [ha]
  exact varint_suffix before remaining r hv

theorem fixed_suffix (before : Slice U8) (width : Nat) : IsSuffix before (fixedResult before width).2 := by
  unfold fixedResult
  split
  · exact suffix_refl before
  · exact ⟨width,by omega,rfl⟩

/-- Every finite actual skip derivation retains a content-exact suffix, not
merely an input-length bound or an error/success flag. -/
theorem skip_suffix {mode tag count before result}
    (trace : SkipSemantics mode tag count before result) : IsSuffix before result.2 := by
  induction trace with
  | limit kind tag before => exact suffix_refl before
  | endField _ => exact suffix_refl _
  | fixed32 _ => exact fixed_suffix _ _
  | fixed64 _ => exact fixed_suffix _ _
  | varint _ hd => exact varint_suffix _ _ _ hd
  | varintError _ hd => exact varint_suffix _ _ _ hd
  | length _ hd => exact suffix_trans (varint_suffix _ _ _ hd) (fixed_suffix _ _)
  | lengthError _ hd => exact varint_suffix _ _ _ hd
  | start _ _ ih => exact ih
  | keyError hd => exact key_suffix _ _ _ hd
  | close hd => unfold groupClose; split <;> exact key_suffix _ _ _ hd
  | childError _ hd _ _ ih => exact suffix_trans (key_suffix _ _ _ hd) ih
  | childNext _ hd _ _ _ ih1 ih2 => exact suffix_trans (suffix_trans (key_suffix _ _ _ hd) ih1) ih2

theorem suffix_absolute {whole after : Slice U8} (h : IsSuffix whole after) :
    after = drop whole (whole.length-after.length) ∧ after.length ≤ whole.length := by
  obtain ⟨used,hu,ha⟩ := h
  have hl : after.length = whole.length-used := by rw [ha,drop_length]
  have he : whole.length-after.length = used := by omega
  exact ⟨by rw [he]; exact ha,by omega⟩

/-- Composition of relative decoder/skip consumption yields one unambiguous
absolute cursor into the original bounded body. -/
theorem suffix_at_cursor (whole : Slice U8) (position : Nat) (after : Slice U8)
    (hp : position ≤ whole.length) (h : IsSuffix (drop whole position) after) :
    ∃ next, position ≤ next ∧ next ≤ whole.length ∧ after = drop whole next ∧
      next = whole.length-after.length := by
  obtain ⟨used,hu,ha⟩ := h
  rw [drop_length] at hu
  refine ⟨position+used,by omega,by omega,?_,?_⟩
  · rw [ha,drop_add]
  · have hl : after.length = whole.length-(position+used) := by rw [ha,drop_length,drop_length]; omega
    omega

#print axioms skip_suffix
#print axioms suffix_absolute
#print axioms suffix_at_cursor
end FullParserV3
