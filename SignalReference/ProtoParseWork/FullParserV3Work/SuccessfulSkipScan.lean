import ProtoParseWork.FullParserV3Work.SkipScanHeaders
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open LoopSupportSkip LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkip
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

/-- Field mode starts before its already justified key; group mode starts after
StartGroup with that tag present in the live frame prefix. Budgets express the
actual pinned default100 recursion convention in both modes. -/
def SuccessfulModeScan (mode : SkipMode) (tag count : U32) (before after : Slice U8) : Prop :=
  match mode with
  | .field kind => ∀ (bytes : Slice U8) (position : Nat) (state : ProtoParse.State (BitVec 8) (BitVec 64)) (tags : List U32),
      position < bytes.length → bytes.length ≤ 512 → StateAt bytes position state tags → tags ≠ [] →
      count.val+tags.length = 100 →
      encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,kind),before) →
      SkipScan bytes position state after tags
  | .group => ∀ (bytes : Slice U8) (position : Nat) (state : ProtoParse.State (BitVec 8) (BitVec 64)) (tags : List U32),
      position < bytes.length → bytes.length ≤ 512 → StateAt bytes position state (tags++[tag]) →
      count.val+tags.length = 100 → before = drop bytes position →
      SkipScan bytes position state after tags

/-- Successful full recursive group/field scan induction. Primitive equalities
come from the actual extracted calls in the derivation, and constructive skip
totality supplies a finite derivation for every contiguous input. Errors retain
the separate full relation and are not claimed by this success subtheorem. -/
theorem successful_skip_scan {mode tag count before result}
    (derivation : SkipSemantics mode tag count before result) (hs : result.1 = .Ok ()) :
    SuccessfulModeScan mode tag count before result.2 := by
  induction derivation with
  | limit => cases hs
  | endField => cases hs
  | @fixed32 tag count before hc =>
    intro bytes position state tags hp hcap hat hn hbudget hk
    have hr := skip_semantics_reference (SkipSemantics.fixed32 (tag := tag) (bytes := before) hc)
    have he : fixedResult before 4 = (.Ok (),(fixedResult before 4).2) := Prod.ext hs rfl
    rw [he] at hr
    exact fixed_skip_scan bytes before _ position tag count .ThirtyTwoBit 4 (Or.inr ⟨rfl,rfl⟩) state tags hp hcap hat hn hc hbudget hk hr
  | @fixed64 tag count before hc =>
    intro bytes position state tags hp hcap hat hn hbudget hk
    have hr := skip_semantics_reference (SkipSemantics.fixed64 (tag := tag) (bytes := before) hc)
    have he : fixedResult before 8 = (.Ok (),(fixedResult before 8).2) := Prod.ext hs rfl
    rw [he] at hr
    exact fixed_skip_scan bytes before _ position tag count .SixtyFourBit 8 (Or.inl ⟨rfl,rfl⟩) state tags hp hcap hat hn hc hbudget hk hr
  | @varint tag count before after value hc hd =>
    intro bytes position state tags hp hcap hat hn hbudget hk
    exact varint_skip_scan bytes before after position tag count value state tags hp hcap hat hn hc hbudget hk hd
  | varintError => cases hs
  | @length tag count before after value hc hd =>
    intro bytes position state tags hp hcap hat hn hbudget hk
    have hr := skip_semantics_reference (SkipSemantics.length (tag := tag) hc hd)
    have he : fixedResult after value.val = (.Ok (),(fixedResult after value.val).2) := Prod.ext hs rfl
    rw [he] at hr
    exact length_skip_scan bytes before _ position tag count state tags hp hcap hat hn hc hbudget hk hr
  | lengthError => cases hs
  | @start tag count before result hc body ih =>
    intro bytes position state tags hp hcap hat hn hbudget hk
    obtain ⟨middle,intermediate,hp',hb,hbefore,hscan,hmid,hfields⟩ :=
      start_header_scan bytes before position tag count state tags hp hcap hat hc hbudget (Or.inl (hat.nested hn)) hk
    have hnonempty := skip_success_decreases body hs
    have hm : middle < bytes.length := by rw [hbefore,drop_length] at hnonempty; omega
    have hrest := ih hs bytes middle intermediate tags hm hcap hmid hbudget hbefore
    exact concat_skip_scan bytes result.2 position middle state intermediate tags hp' hscan hfields hrest
  | keyError => cases hs
  | @close tag inner count before after hd =>
    intro bytes position state tags hp hcap hat hbudget hbefore
    have he : inner = tag := by
      by_contra hn
      simp only [groupClose,if_neg hn] at hs
      cases hs
    subst inner
    simp only [groupClose,if_pos rfl]
    apply end_header_scan bytes after position tag state tags hp hcap hat
    simpa only [hbefore] using hd
  | childError => cases hs
  | @childNext tag inner count child before middle after kind result hk hd hc body rest ihChild ihRest =>
    intro bytes position state tags hp hcap hat hbudget hbefore
    have hchildBudget : child.val+(tags++[tag]).length = 100 := by
      simp only [List.length_append,List.length_singleton]; omega
    have hkey : encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (inner,kind),middle) := by simpa only [hbefore] using hd
    have hnonempty : tags++[tag] ≠ [] := by simp
    have hchild := ihChild rfl bytes position state (tags++[tag]) hp hcap hat hnonempty hchildBudget hkey
    obtain ⟨mid,intermediate,hp',hb,hafter,hscan,hmid,hfields⟩ := hchild
    change after = drop bytes mid at hafter
    have hstrict := skip_success_decreases rest hs
    have hm : mid < bytes.length := by rw [hafter,drop_length] at hstrict; omega
    have hrest := ihRest hs bytes mid intermediate tags hm hcap hmid hbudget hafter
    exact concat_skip_scan bytes result.2 position mid state intermediate tags hp' hscan hfields hrest

#print axioms successful_skip_scan
end FullParserV3
