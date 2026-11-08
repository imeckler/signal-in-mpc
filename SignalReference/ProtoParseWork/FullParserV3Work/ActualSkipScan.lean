import ProtoParseWork.FullParserV3Work.SuccessfulSkipScan
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open LoopSupportSkip LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkip
set_option maxHeartbeats 3000000

/-- Actual successful skip_field, with no finite-derivation, primitive-correctness
or termination premise, agrees with the complete nested public scan interval. -/
theorem actual_nested_skip_scan (bytes before after : Slice U8) (position : Nat) (tag count : U32)
    (kind : encoding.wire_type.WireType) (state : ProtoParse.State (BitVec 8) (BitVec 64)) (tags : List U32)
    (hp : position < bytes.length) (hcap : bytes.length ≤ 512)
    (hat : StateAt bytes position state tags) (hn : tags ≠ []) (hbudget : count.val+tags.length = 100)
    (hk : encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,kind),before))
    (hskip : encoding.skip_field sliceBuf kind tag before ⟨count⟩ = .ok (.Ok (),after)) :
    SkipScan bytes position state after tags := by
  obtain ⟨result,hsem,hr,_⟩ := skip_field_total kind tag count before
  rw [hskip] at hr
  cases hr
  exact successful_skip_scan hsem rfl bytes position state tags hp hcap hat hn hbudget hk

/-- The actual recursive group loop agrees with its complete bounded scan,
including nested groups and all ordinary supported wire types on success. -/
theorem actual_group_success_scan (bytes before after : Slice U8) (position : Nat) (tag count : U32)
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (tags : List U32)
    (hp : position < bytes.length) (hcap : bytes.length ≤ 512)
    (hat : StateAt bytes position state (tags++[tag])) (hbudget : count.val+tags.length = 100)
    (hbefore : before = drop bytes position)
    (hskip : encoding.skip_field_loop sliceBuf tag before ⟨count⟩ = .ok (.Ok (),after)) :
    SkipScan bytes position state after tags := by
  have hb : tags.length+1 ≤ 100 := by simpa only [List.length_append,List.length_singleton] using hat.frames.bound.trans hat.frames.limit
  have hc : count ≠ 0#u32 := by intro hz; rw [hz] at hbudget; change 0+tags.length=100 at hbudget; omega
  obtain ⟨result,hsem,hr,_⟩ := skip_group_total tag count before hc
  rw [hskip] at hr
  cases hr
  exact successful_skip_scan hsem rfl bytes position state tags hp hcap hat hbudget hbefore

/-- A successful unknown top-level StartGroup (or any nested StartGroup) opens,
scans and closes against actual Rust, restoring the prior live frame prefix. -/
theorem actual_start_group_scan (bytes before after : Slice U8) (position : Nat) (tag count : U32)
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (tags : List U32)
    (hp : position < bytes.length) (hcap : bytes.length ≤ 512)
    (hat : StateAt bytes position state tags) (hbudget : count.val+tags.length = 100)
    (hskipAllowed : state.depth ≠ 0 ∨ 6 < tag.val)
    (hk : encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,.StartGroup),before))
    (hskip : encoding.skip_field sliceBuf .StartGroup tag before ⟨count⟩ = .ok (.Ok (),after)) :
    SkipScan bytes position state after tags := by
  have hc : count ≠ 0#u32 := by intro hz; subst count; rw [recursion_limit_first] at hskip; cases hskip
  obtain ⟨result,hsem,hr,_⟩ := skip_field_total .StartGroup tag count before
  rw [hskip] at hr
  cases hr
  have hnonempty := skip_success_decreases hsem rfl
  obtain ⟨middle,intermediate,hp',hb,hbefore,hscan,hmid,hfields⟩ := start_header_scan bytes before position tag count state tags
    hp hcap hat hc hbudget hskipAllowed hk
  have hm : middle < bytes.length := by rw [hbefore,drop_length] at hnonempty; omega
  have hloop : encoding.skip_field_loop sliceBuf tag before ⟨count⟩ = .ok (.Ok (),after) := by
    rw [← start_group before tag count hc]
    exact hskip
  have hrest := actual_group_success_scan bytes before after middle tag count intermediate tags hm hcap hmid hbudget hbefore hloop
  exact concat_skip_scan bytes after position middle state intermediate tags hp' hscan hfields hrest

#print axioms actual_nested_skip_scan
#print axioms actual_group_success_scan
#print axioms actual_start_group_scan
end FullParserV3
