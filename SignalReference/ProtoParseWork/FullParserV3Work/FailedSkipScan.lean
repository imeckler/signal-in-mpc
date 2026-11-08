import ProtoParseWork.FullParserV3Work.SkipFailureHeaders
import ProtoParseWork.FullParserV3Work.SuccessfulSkipScan
import ProtoParseWork.FullParserV3Work.SkipTotality
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3.Observed
open SignalMessageIntegration DispatcherIntegration
open LoopSupportSkip LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkip
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

private theorem successful_key_nonempty (before middle : Slice U8) (tag : U32)
    (kind : encoding.wire_type.WireType)
    (hd : encoding.decode_key sliceBuf before = .ok (.Ok (tag,kind),middle)) : 0 < before.length := by
  obtain ⟨r,after,hr,_,hlt⟩ := key_total before
  rw [hd] at hr
  cases hr
  have h := hlt (tag,kind) rfl
  omega

private theorem scan_fields_congr (bytes after : Slice U8) (position : Nat) (state : State (BitVec 8) (BitVec 64))
    (error : prost.error.DecodeError) (left right : List (ProtoParse.Field (BitVec 8) (BitVec 64)))
    (he : left = right) (h : RejectedScan bytes position state after error left) :
    RejectedScan bytes position state after error right := he ▸ h

/-- Field mode starts before an actual decoded key, and permits precisely
nested skipped fields or unknown top-level tags. EndGroup is a field error only
at top level; actual group loops test a closing tag before child recursion. -/
def FailedModeScan (mode : SkipMode) (tag count : U32) (before after : Slice U8)
    (error : LoopSupportSkip.error.DecodeError) : Prop :=
  match mode with
  | .field kind => ∀ (bytes : Slice U8) (position : Nat) (state : State (BitVec 8) (BitVec 64)) (tags : List U32),
      position < bytes.length → bytes.length ≤ 512 → StateAt bytes position state.parser tags →
      count.val+tags.length = 100 → (state.parser.depth ≠ 0 ∨ 6 < tag.val) →
      (kind ≠ .EndGroup ∨ tags = []) →
      encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,kind),before) →
      RejectedScan bytes position state after (skipError error) state.parser.fields
  | .group => ∀ (bytes : Slice U8) (position : Nat) (state : State (BitVec 8) (BitVec 64)) (tags : List U32),
      position ≤ bytes.length → bytes.length ≤ 512 → StateAt bytes position state.parser (tags++[tag]) →
      count.val+tags.length = 100 → before = drop bytes position →
      RejectedScan bytes position state after (skipError error) state.parser.fields

/-- Complete recursive skip rejection induction. Its finite derivation is
constructively supplied by SkipTotality, and every primitive/error premise is
an actual extracted call. No success-only observation or termination axiom. -/
theorem failed_skip_scan {mode tag count before result}
    (derivation : SkipSemantics mode tag count before result) :
    ∀ error, result.1 = .Err error → FailedModeScan mode tag count before result.2 error := by
  induction derivation with
  | limit kind tag before =>
    intro error hs
    cases hs
    intro bytes position state tags hp hcap hat hbudget ha hend hk
    have hlen : tags.length = 100 := by change 0+tags.length = 100 at hbudget; omega
    have hkind : kind ≠ .EndGroup := hend.resolve_right (by intro hz; rw [hz] at hlen; simp at hlen)
    exact skipped_limit_failure bytes before before position tag kind hkind _ state tags hp hcap hat hlen hk (recursion_limit_first sliceBuf kind tag before)
  | @endField tag count before hc =>
    intro error hs
    cases hs
    intro bytes position state tags hp hcap hat hbudget ha hend hk
    have hz : tags = [] := hend.resolve_left (by intro h; exact h rfl)
    subst tags
    have hd : state.parser.depth = 0 := hat.frames.depth_eq
    have ht : 6 < tag.val := ha.resolve_left (not_not.mpr hd)
    exact top_end_failure_scan bytes before before position tag count _ state hp hcap hat ht hc hk (unexpected_end_group sliceBuf tag before count hc)
  | @fixed32 tag count before hc =>
    intro error hs
    intro bytes position state tags hp hcap hat hbudget ha hend hk
    have hr := skip_semantics_reference (SkipSemantics.fixed32 (tag := tag) (bytes := before) hc)
    have he : fixedResult before 4 = (.Err error,(fixedResult before 4).2) := Prod.ext hs rfl
    rw [he] at hr
    exact skipped_fixed_failure bytes before _ position tag count .ThirtyTwoBit 4 (Or.inr ⟨rfl,rfl⟩) error state tags hp hcap hat hc hbudget ha hk hr
  | @fixed64 tag count before hc =>
    intro error hs
    intro bytes position state tags hp hcap hat hbudget ha hend hk
    have hr := skip_semantics_reference (SkipSemantics.fixed64 (tag := tag) (bytes := before) hc)
    have he : fixedResult before 8 = (.Err error,(fixedResult before 8).2) := Prod.ext hs rfl
    rw [he] at hr
    exact skipped_fixed_failure bytes before _ position tag count .SixtyFourBit 8 (Or.inl ⟨rfl,rfl⟩) error state tags hp hcap hat hc hbudget ha hk hr
  | varint hc hd => intro error hs; cases hs
  | @varintError tag count before after native hc hd =>
    intro error hs
    cases hs
    intro bytes position state tags hp hcap hat hbudget ha hend hk
    exact skipped_payload_failure bytes before after position tag count .Varint native state tags hp hcap hat hc hbudget ha (Or.inl rfl) hk hd
  | @length tag count before rest raw hc hd =>
    intro error hs
    intro bytes position state tags hp hcap hat hbudget ha hend hk
    have hr := skip_semantics_reference (SkipSemantics.length (tag := tag) hc hd)
    have he : fixedResult rest raw.val = (.Err error,(fixedResult rest raw.val).2) := Prod.ext hs rfl
    rw [he] at hr
    exact skipped_length_failure bytes before rest _ position tag count raw error state tags hp hcap hat hc hbudget ha hk hd hr
  | @lengthError tag count before after native hc hd =>
    intro error hs
    cases hs
    intro bytes position state tags hp hcap hat hbudget ha hend hk
    exact skipped_payload_failure bytes before after position tag count .LengthDelimited native state tags hp hcap hat hc hbudget ha (Or.inr rfl) hk hd
  | @start tag count before result hc body ih =>
    intro error hs
    intro bytes position state tags hp hcap hat hbudget ha hend hk
    obtain ⟨middle,intermediate,hp',hb,hbefore,hscan,hmid,hfields⟩ :=
      start_header_scan bytes before position tag count state.parser tags hp hcap hat hc hbudget ha hk
    have hr := ih error hs bytes middle ⟨intermediate,state.error⟩ tags hb hcap hmid hbudget hbefore
    have hr' := scan_fields_congr bytes result.2 middle ⟨intermediate,state.error⟩ (skipError error) _ _ hfields hr
    exact rejected_scan_prefix bytes result.2 position middle state intermediate (skipError error) state.parser.fields hp'.le hb hat.ok hat.fields_mask hscan hmid.ok hr'
  | @keyError tag count before after native hd =>
    intro error hs
    cases hs
    intro bytes position state tags hp hcap hat hbudget hbefore
    have hd' : encoding.decode_key sliceBuf (drop bytes position) = .ok (.Err native,after) := by simpa only [hbefore] using hd
    by_cases hl : position < bytes.length
    · exact key_failure_scan bytes after position native state (tags++[tag]) hl hcap hat hd'
    · have he : position = bytes.length := by omega
      subst position
      exact eof_rejected_scan bytes after native state (tags++[tag]) hcap hat (by simp) hd'
  | @close tag inner count before after hd =>
    intro error hs
    intro bytes position state tags hp hcap hat hbudget hbefore
    have hd' : encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (inner,.EndGroup),after) := by simpa only [hbefore] using hd
    have hn := successful_key_nonempty (drop bytes position) after inner .EndGroup hd'
    rw [drop_length] at hn
    have hl : position < bytes.length := by omega
    have hb := group_end_after (drop bytes position) after tag inner ⟨count⟩ hd'
    have he : groupClose tag inner after = (.Err error,(groupClose tag inner after).2) := Prod.ext hs rfl
    rw [he] at hb
    exact mismatched_group_failure_scan bytes after _ position tag inner count error state tags hl hcap hat hd' hb
  | @childError tag inner count child before middle after kind native hk hd hc body ih =>
    intro error hs
    cases hs
    intro bytes position state tags hp hcap hat hbudget hbefore
    have hchildBudget : child.val+(tags++[tag]).length = 100 := by simp only [List.length_append,List.length_singleton]; omega
    have hd' : encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (inner,kind),middle) := by simpa only [hbefore] using hd
    have hn := successful_key_nonempty (drop bytes position) middle inner kind hd'
    rw [drop_length] at hn
    have hl : position < bytes.length := by omega
    exact ih native rfl bytes position state (tags++[tag]) hl hcap hat hchildBudget
      (Or.inl (hat.nested (by simp))) (Or.inl hk) hd'
  | @childNext tag inner count child before middle after kind result hk hd hc body rest ihChild ihRest =>
    intro error hs
    intro bytes position state tags hp hcap hat hbudget hbefore
    have hchildBudget : child.val+(tags++[tag]).length = 100 := by simp only [List.length_append,List.length_singleton]; omega
    have hd' : encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (inner,kind),middle) := by simpa only [hbefore] using hd
    have hn := successful_key_nonempty (drop bytes position) middle inner kind hd'
    rw [drop_length] at hn
    have hl : position < bytes.length := by omega
    have hchild := successful_skip_scan body rfl bytes position state.parser (tags++[tag]) hl hcap hat (by simp) hchildBudget hd'
    obtain ⟨mid,intermediate,hp',hb,hafter,hscan,hmid,hfields⟩ := hchild
    have hr := ihRest error hs bytes mid ⟨intermediate,state.error⟩ tags hb hcap hmid hbudget hafter
    have hr' := scan_fields_congr bytes result.2 mid ⟨intermediate,state.error⟩ (skipError error) _ _ hfields hr
    exact rejected_scan_prefix bytes result.2 position mid state intermediate (skipError error) state.parser.fields hp'.le hb hat.ok hat.fields_mask hscan hmid.ok hr'

#print axioms failed_skip_scan
end FullParserV3.Observed
