import ProtoParseWork.FullParserV3Work.Suffix
open Aeneas Aeneas.Std
namespace FullParserV3
open LoopSupportSkip LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkip
set_option maxHeartbeats 2000000

theorem skip_nonincrease {mode tag count before result} (h : SkipSemantics mode tag count before result) :
    result.2.length ≤ before.length := by
  obtain ⟨used,_,he⟩ := skip_suffix h
  rw [he,drop_length]
  omega

theorem varint_success_decreases (before after : Slice U8) (value : U64)
    (hd : encoding.varint.decode_varint sliceBuf before = .ok (.Ok value,after)) : after.length < before.length := by
  obtain ⟨r,rest,hr,_,hlt⟩ := varint_total before
  rw [hd] at hr
  cases hr
  exact hlt value rfl

theorem key_success_decreases (before after : Slice U8) (tag : U32) (kind : encoding.wire_type.WireType)
    (hd : encoding.decode_key sliceBuf before = .ok (.Ok (tag,kind),after)) : after.length < before.length := by
  obtain ⟨r,rest,hr,_,hlt⟩ := key_total before
  rw [hd] at hr
  cases hr
  exact hlt (tag,kind) rfl

private theorem fixed_success_decreases (before : Slice U8) (width : Nat) (hw : 0 < width)
    (hs : (fixedResult before width).1 = .Ok ()) : (fixedResult before width).2.length < before.length := by
  unfold fixedResult at *
  split at hs
  · cases hs
  · rename_i hn
    rw [if_neg hn,drop_length]
    omega

/-- Every successful finite skip consumes input, including empty bytes and
empty groups. This derives the nonempty remainder obligations in group scan
induction without assuming termination or successful decoder correctness. -/
theorem skip_success_decreases {mode tag count before result}
    (derivation : SkipSemantics mode tag count before result) (hs : result.1 = .Ok ()) :
    result.2.length < before.length := by
  induction derivation with
  | limit => cases hs
  | endField => cases hs
  | fixed32 => exact fixed_success_decreases _ 4 (by decide) hs
  | fixed64 => exact fixed_success_decreases _ 8 (by decide) hs
  | varint _ hd => exact varint_success_decreases _ _ _ hd
  | varintError => cases hs
  | @length tag count before after value hc hd =>
    have h := varint_success_decreases _ _ _ hd
    have hb := fixed_nonincrease after value.val
    omega
  | lengthError => cases hs
  | start _ _ ih => exact ih hs
  | keyError => cases hs
  | close hd =>
    have h := key_success_decreases _ _ _ _ hd
    unfold groupClose
    split <;> exact h
  | childError => cases hs
  | childNext _ hd _ body rest _ _ =>
    have hk := key_success_decreases _ _ _ _ hd
    have hc := skip_nonincrease body
    have hr := skip_nonincrease rest
    dsimp only at hc hr
    omega

#print axioms skip_nonincrease
#print axioms skip_success_decreases
end FullParserV3
