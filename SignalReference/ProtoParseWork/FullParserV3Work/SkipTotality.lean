import ProtoParseWork.FullParserV3Work.Skip.SkipSemantics
import ProtoParseWork.FullParserV3Work.DecoderTable
open Aeneas Aeneas.Std Result TlsMpc TlsMpc.Signal
open LoopSupportSkip
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkip
open LibSignalReference.Candidate.ProstSkipKey
open LibSignalReference.Candidate.ProstTopField
namespace FullParserV3
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem varint_total (before : Slice U8) :
    ∃ result after,
      encoding.varint.decode_varint sliceBuf before = ok (result,after) ∧
      after.length ≤ before.length ∧
      (∀ value, result = .Ok value → after.length < before.length) := by
  obtain ⟨result,after,hd,hp,he⟩ := decode_full_reference before
  refine ⟨result,after,hd,?_⟩
  cases result with
  | Ok value =>
    obtain ⟨count,hc,h10,hprefix,hrest⟩ := hp
    have hpos := prefix_count_positive before count value h10 hprefix
    rw [hrest,drop_length]
    exact ⟨by omega,fun _ _ => by omega⟩
  | Err error =>
    have hr : after = if FastGuard before then before else drop before (min 10 before.length) := he
    refine ⟨?_,?_⟩
    · rw [hr]; split <;> try simp only [drop_length]
      all_goals omega
    · intro value h; cases h

theorem key_total (before : Slice U8) :
    ∃ result after,
      encoding.decode_key sliceBuf before = ok (result,after) ∧
      after.length ≤ before.length ∧
      (∀ pair, result = .Ok pair → after.length < before.length) := by
  obtain ⟨result,after,hd,hle,hlt⟩ := varint_total before
  refine ⟨finishResult result,after,key_from_varint _ _ _ hd,hle,?_⟩
  intro pair h
  cases result with
  | Err e => cases h
  | Ok value => exact hlt value rfl

theorem fixed_nonincrease (before : Slice U8) (width : Nat) :
    (fixedResult before width).2.length ≤ before.length := by
  unfold fixedResult
  split <;> simp only [drop_length] <;> omega

/-- A mode rank handles the non-consuming StartGroup -> group transition.
Every group iteration first consumes a nonempty successful key; its child and
remaining group both have strictly smaller input even if a skip consumes zero. -/
def modeRank : SkipMode → Nat
  | .field _ => 1
  | .group => 0

/-- Total finite skip derivations on every valid contiguous U8 slice and U32
recursion budget. There is no decoder/skip equality or termination premise. -/
theorem skip_total_with_bound (fuel : Nat) :
    ∀ (mode : SkipMode) (tag count : U32) (before : Slice U8),
      (mode = .group → count ≠ 0#u32) →
      2 * before.length + modeRank mode = fuel →
      ∃ result, SkipSemantics mode tag count before result ∧ result.2.length ≤ before.length := by
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro mode tag count before hmode hf
    cases mode with
    | field kind =>
      by_cases hz : count = 0#u32
      · subst count
        exact ⟨_,SkipSemantics.limit kind tag before,by rfl⟩
      · cases kind with
        | EndGroup => exact ⟨_,SkipSemantics.endField hz,by rfl⟩
        | ThirtyTwoBit => exact ⟨_,SkipSemantics.fixed32 hz,fixed_nonincrease before 4⟩
        | SixtyFourBit => exact ⟨_,SkipSemantics.fixed64 hz,fixed_nonincrease before 8⟩
        | Varint =>
          obtain ⟨result,after,hd,hle,_⟩ := varint_total before
          cases result with
          | Ok value => exact ⟨_,SkipSemantics.varint hz hd,hle⟩
          | Err error => exact ⟨_,SkipSemantics.varintError hz hd,hle⟩
        | LengthDelimited =>
          obtain ⟨result,after,hd,hle,_⟩ := varint_total before
          cases result with
          | Ok value => exact ⟨_,SkipSemantics.length hz hd,(fixed_nonincrease after value.val).trans hle⟩
          | Err error => exact ⟨_,SkipSemantics.lengthError hz hd,hle⟩
        | StartGroup =>
          obtain ⟨result,hbody,hle⟩ := ih (2*before.length) (by simp only [modeRank] at hf; omega)
            .group tag count before (fun _ => hz) rfl
          exact ⟨result,SkipSemantics.start hz hbody,hle⟩
    | group =>
      obtain ⟨result,middle,hkey,hle,hlt⟩ := key_total before
      cases result with
      | Err error => exact ⟨_,SkipSemantics.keyError hkey,hle⟩
      | Ok pair =>
        rcases pair with ⟨inner,kind⟩
        have hshort := hlt (inner,kind) rfl
        by_cases hend : kind = .EndGroup
        · subst kind
          refine ⟨_,SkipSemantics.close hkey,?_⟩
          unfold groupClose; split <;> exact hle
        · have hz : count ≠ 0#u32 := hmode rfl
          let child := U32.ofNatCore (count.val-1) (by have h := count.hmax; scalar_tac)
          have hc : count.val = child.val + 1 := by
            have hp : 0 < count.val := by
              by_contra hn
              have he : count = 0#u32 := by apply UScalar.eq_of_val_eq; scalar_tac
              exact hz he
            change count.val = (count.val-1) + 1
            omega
          obtain ⟨childResult,hchild,hchildBound⟩ := ih (2*middle.length+1)
            (by simp only [modeRank] at hf; omega) (.field kind) inner child middle (by intro h; cases h) rfl
          cases childResult with
          | mk status after =>
            cases status with
            | Err error => exact ⟨_,SkipSemantics.childError hend hkey hc hchild,hchildBound.trans hle⟩
            | Ok unit =>
              cases unit
              change after.length ≤ middle.length at hchildBound
              obtain ⟨result,hrest,hrbound⟩ := ih (2*after.length)
                (by simp only [modeRank] at hf; omega) .group tag count after (fun _ => hz) rfl
              exact ⟨result,SkipSemantics.childNext hend hkey hc hchild hrest,hrbound.trans (hchildBound.trans hle)⟩
/-- Every actual skip_field call terminates with an ordinary protobuf result.
Zero budget is covered by the actual RecursionLimitReached branch. -/
theorem skip_field_total (kind : encoding.wire_type.WireType) (tag count : U32) (before : Slice U8) :
    ∃ result, SkipSemantics (.field kind) tag count before result ∧
      encoding.skip_field sliceBuf kind tag before ⟨count⟩ = ok result ∧
      result.2.length ≤ before.length := by
  obtain ⟨result,hsem,hle⟩ := skip_total_with_bound (2*before.length+1)
    (.field kind) tag count before (by intro h; cases h) rfl
  exact ⟨result,hsem,skip_semantics_reference hsem,hle⟩

theorem skip_group_total (tag count : U32) (before : Slice U8) (hc : count ≠ 0#u32) :
    ∃ result, SkipSemantics .group tag count before result ∧
      encoding.skip_field_loop sliceBuf tag before ⟨count⟩ = ok result ∧
      result.2.length ≤ before.length := by
  obtain ⟨result,hsem,hle⟩ := skip_total_with_bound (2*before.length)
    .group tag count before (fun _ => hc) rfl
  exact ⟨result,hsem,skip_semantics_reference hsem,hle⟩

theorem skip_deterministic {mode tag count before left right}
    (hl : SkipSemantics mode tag count before left)
    (hr : SkipSemantics mode tag count before right) : left = right := by
  have h := (skip_semantics_reference hl).symm.trans (skip_semantics_reference hr)
  exact Result.ok.inj h

#print axioms varint_total
#print axioms key_total
#print axioms skip_field_total
#print axioms skip_group_total
#print axioms skip_deterministic

end FullParserV3
