import ProtoParseWork.FullParserV3Work.FrozenRejection
import ProtoParseWork.FullParserV3Work.GroupHeaderScan
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3.Observed
open SignalMessageIntegration DispatcherIntegration
open LoopSupportSkip LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkip
open LibSignalReference.Candidate.ProstSkipKey LibSignalReference.Candidate.ProstSkipPlan LibSignalReference.Candidate.ProstTopField
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

private theorem bounded_cursor_nat (cursor capacity : Nat) (hc : cursor ≤ capacity) (hcap : capacity ≤ 512) :
    (BitVec.ofNat 64 cursor).toNat = cursor := by
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]

private theorem mismatched_end_plan (capacity position : Nat) (last : BitVec 8)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hk : key.ok = 255)
    (hr : key.value.toNat ≤ 4294967295) (hn : key.value >>> 3 ≠ 0)
    (h4 : key.value &&& 7 = 4) (hd : state.depth ≠ 0)
    (hw : key.value >>> 3 ≠ ProtoParse.lookupWord Word64.concrete ByteAuth.concrete (state.depth-1) 0 state.stack) :
    let p := ProtoParse.planWithCursor Word64.concrete ByteAuth.concrete capacity position last key payload state
    p.ok = 0 ∧ p.stop = key.stop := by
  have hb : (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok = 0 := by
    rw [end_in_group capacity key payload state hk hr hn h4 hd,if_neg hw]
  have h0 : key.value &&& 7 ≠ 0 := by rw [h4]; decide
  have h2 : key.value &&& 7 ≠ 2 := by rw [h4]; decide
  exact ⟨hb,nonpayload_failure_stop capacity position last key payload state hk hb
    (nonpayload_mask key state (Or.inr (Or.inr ⟨h0,h2⟩)))⟩

private theorem group_close_error_values (outer inner : U32) (middle after : Slice U8)
    (error : LoopSupportSkip.error.DecodeError) (hclose : (.Err error,after) = groupClose outer inner middle) :
    inner ≠ outer ∧ error = decodeError .UnexpectedEndGroupTag ∧ after = middle := by
  by_cases hm : inner = outer
  · subst inner
    simp only [groupClose,if_pos rfl] at hclose
    cases hclose
  · simp only [groupClose,if_neg hm] at hclose
    exact ⟨hm,core.result.Result.Err.inj (congrArg Prod.fst hclose),congrArg Prod.snd hclose⟩

private theorem nonempty_frame_depth (depth : BitVec 64) (stack : List (BitVec 64))
    (tags : List U32) (outer : U32) (hf : Frames depth stack (tags++[outer])) : depth ≠ 0 := by
  have hframesBound := hf.bound.trans hf.limit
  intro hz
  have hd := congrArg BitVec.toNat (hf.depth_eq.symm.trans hz)
  change (tags++[outer]).length % 2^64 = 0 at hd
  rw [Nat.mod_eq_of_lt (by omega)] at hd
  simp only [List.length_append,List.length_singleton] at hd
  omega

private theorem mismatch_frame_word (value depth : BitVec 64) (stack : List (BitVec 64))
    (tags : List U32) (outer inner : U32) (hf : Frames depth stack (tags++[outer]))
    (htag : value >>> 3 = BitVec.ofNat 64 inner.val) (hmismatch : inner ≠ outer) :
    value >>> 3 ≠ ProtoParse.lookupWord Word64.concrete ByteAuth.concrete (depth-1) 0 stack := by
  have hiBound : inner.val < 2^64 := by have h := inner.bv.isLt; simp only [UScalar.bv_toNat] at h; omega
  have hoBound : outer.val < 2^64 := by have h := outer.bv.isLt; simp only [UScalar.bv_toNat] at h; omega
  rw [htag,frames_top outer hf]
  intro he
  apply hmismatch
  apply UScalar.eq_of_val_eq
  have hv := congrArg BitVec.toNat he
  simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hiBound,Nat.mod_eq_of_lt hoBound] using hv

/-- Actual mismatched closing-tag rejection from the group loop retains all
fields and live frames, consumes exactly the closing key, and records the exact
UnexpectedEndGroupTag constructor. Depth100 closes are checked before recursion. -/
theorem actual_group_end_rejection_step (bytes middle after : Slice U8) (position : Nat) (outer inner count : U32)
    (tags : List U32) (error : LoopSupportSkip.error.DecodeError) (state : State (BitVec 8) (BitVec 64))
    (hp : position < bytes.length) (hcap : bytes.length ≤ 512)
    (hs : state.parser.ok = 255) (hn : state.parser.next = BitVec.ofNat 64 position)
    (hf : Frames state.parser.depth state.parser.stack (tags++[outer]))
    (hk : encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (inner,.EndGroup),middle))
    (hbody : encoding.skip_field_loop.body sliceBuf outer ⟨count⟩ (drop bytes position) = .ok (.done (.Err error,after))) :
    ∀ positions : List Nat, ActiveRejection bytes after (skipError error) state
      (finish Word64.concrete ByteAuth.concrete (positions.foldl (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes))
        (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes) state position))) state.parser.fields := by
  let key := (rowsOf bytes)[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩
  let payload := ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete key.stop (position+1) (((rowsOf bytes).drop (position+1)).take 10)
  let p := planOf bytes position state.parser
  obtain ⟨kc,_,_,hkb,hrest,hkok,hkstop,hkrange,hknz,htag,hkind,hkmask⟩ := actual_key_row bytes middle position inner .EndGroup hp hk
  have hr := group_end_after (drop bytes position) middle outer inner ⟨count⟩ hk
  rw [hbody] at hr
  have hclose := ControlFlow.done.inj (Result.ok.inj hr)
  obtain ⟨hmismatch,herr,hafter⟩ := group_close_error_values outer inner middle after error hclose
  have hdepth := nonempty_frame_depth state.parser.depth state.parser.stack tags outer hf
  have hword := mismatch_frame_word key.value state.parser.depth state.parser.stack tags outer inner hf htag hmismatch
  have hkind4 : key.value &&& 7 = 4 := hkind
  obtain ⟨hp0,hstop⟩ := mismatched_end_plan bytes.length position
    ((rowsOf bytes)[bytes.length-1]?.getD ⟨0,BitVec.ofNat 64 (bytes.length-1),0⟩).ok key payload state.parser
    hkok hkrange hknz hkind4 hdepth hword
  change p.ok = 0 at hp0
  change p.stop = key.stop at hstop
  have hstart : key.stop.toNat = position+kc := by rw [hkstop]; exact bounded_cursor_nat _ _ hkb hcap
  have ha : after = drop bytes p.stop.toNat := by rw [hstop,hstart,hafter]; exact hrest
  have hb : p.stop.toNat ≤ bytes.length := by rw [hstop,hstart]; exact hkb
  have hvalid : (key.value &&& 7).toNat ≤ 5 := by rw [hkind4]; decide
  have hm : statusView (.Err (skipError error)) = some (classifiedAt bytes position state.parser) := by
    change statusView (.Err (skipError error)) = some (classify Word64.concrete ByteAuth.concrete key payload state.parser)
    rw [classify_valid_header key payload state.parser hkok hkrange hknz hvalid,
      field_classify_known_wire key payload state.parser (valid_known_skip key state.parser (Or.inl hdepth)),
      skip_code_end key payload state.parser hkind4,herr]
    rfl
  intro positions
  have h := freeze_active_reject bytes after position (skipError error) state hs hn hp0 ha hb hm positions
  change ActiveRejection bytes after (skipError error) state _
    (if state.parser.depth = 0 then ProtoParse.initializeFields Word64.concrete ByteAuth.concrete 255 p.tag state.parser.fields else state.parser.fields) at h
  have hfields : (if state.parser.depth = 0 then ProtoParse.initializeFields Word64.concrete ByteAuth.concrete 255 p.tag state.parser.fields else state.parser.fields) = state.parser.fields := if_neg hdepth
  exact Eq.mp (congrArg (fun fields => ActiveRejection bytes after (skipError error) state
    (finish Word64.concrete ByteAuth.concrete (positions.foldl (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes))
      (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes) state position))) fields) hfields) h

/-- An actual top-level unknown EndGroup rejects before payload decoding,
without modifying any message Option. Known wrong-wire EndGroups are distinct. -/
theorem actual_top_end_rejection_step (bytes middle after : Slice U8) (position : Nat) (tag count : U32)
    (error : LoopSupportSkip.error.DecodeError) (state : State (BitVec 8) (BitVec 64))
    (hp : position < bytes.length) (hcap : bytes.length ≤ 512)
    (hs : state.parser.ok = 255) (hn : state.parser.next = BitVec.ofNat 64 position)
    (hl : state.parser.fields.length = 6) (hdepth : state.parser.depth = 0) (ht : 6 < tag.val) (hc : count ≠ 0#u32)
    (hk : encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,.EndGroup),middle))
    (hskip : encoding.skip_field sliceBuf .EndGroup tag middle ⟨count⟩ = .ok (.Err error,after)) :
    ∀ positions : List Nat, ActiveRejection bytes after (skipError error) state
      (finish Word64.concrete ByteAuth.concrete (positions.foldl (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes))
        (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes) state position))) state.parser.fields := by
  let key := (rowsOf bytes)[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩
  let payload := ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete key.stop (position+1) (((rowsOf bytes).drop (position+1)).take 10)
  let p := planOf bytes position state.parser
  obtain ⟨kc,_,_,hkb,hrest,hkok,hkstop,hkrange,hknz,htag,hkind,hkmask⟩ := actual_key_row bytes middle position tag .EndGroup hp hk
  rw [unexpected_end_group sliceBuf tag middle count hc] at hskip
  have herr : error = decodeError .UnexpectedEndGroupTag := (core.result.Result.Err.inj (congrArg Prod.fst (Result.ok.inj hskip))).symm
  have hafter : after = middle := (congrArg Prod.snd (Result.ok.inj hskip)).symm
  have hkind4 : key.value &&& 7 = 4 := hkind
  have hbad := top_end_reject bytes.length key payload state.parser hdepth hkind4
  have hp0 : p.ok = 0 := hbad
  have h0 : key.value &&& 7 ≠ 0 := by rw [hkind4]; decide
  have h2 : key.value &&& 7 ≠ 2 := by rw [hkind4]; decide
  have hstop : p.stop = key.stop := nonpayload_failure_stop _ _ _ key payload state.parser hkok hbad
    (nonpayload_mask key state.parser (Or.inr (Or.inr ⟨h0,h2⟩)))
  have hstart : key.stop.toNat = position+kc := by rw [hkstop]; exact bounded_cursor_nat _ _ hkb hcap
  have ha : after = drop bytes p.stop.toNat := by rw [hstop,hstart,hafter]; exact hrest
  have hb : p.stop.toNat ≤ bytes.length := by rw [hstop,hstart]; exact hkb
  have htBound : tag.val < 2^64 := by have h := tag.bv.isLt; simp only [UScalar.bv_toNat] at h; omega
  have hunknown : 6 < (key.value >>> 3).toNat := by rw [htag,BitVec.toNat_ofNat,Nat.mod_eq_of_lt htBound]; exact ht
  have hvalid : (key.value &&& 7).toNat ≤ 5 := by rw [hkind4]; decide
  have hm : statusView (.Err (skipError error)) = some (classifiedAt bytes position state.parser) := by
    change statusView (.Err (skipError error)) = some (classify Word64.concrete ByteAuth.concrete key payload state.parser)
    rw [classify_valid_header key payload state.parser hkok hkrange hknz hvalid,
      field_classify_known_wire key payload state.parser (valid_known_skip key state.parser (Or.inr hunknown)),
      skip_code_end key payload state.parser hkind4,herr]
    rfl
  have htag' : p.tag = key.value >>> 3 := plan_valid_tag _ _ _ _ _ _ hkmask
  have hfields : (if state.parser.depth = 0 then ProtoParse.initializeFields Word64.concrete ByteAuth.concrete 255 p.tag state.parser.fields else state.parser.fields) = state.parser.fields := by
    rw [if_pos hdepth]
    apply initialize_unknown state.parser.fields p.tag (by omega)
    rw [htag']; exact hunknown
  intro positions
  have h := freeze_active_reject bytes after position (skipError error) state hs hn hp0 ha hb hm positions
  change ActiveRejection bytes after (skipError error) state _
    (if state.parser.depth = 0 then ProtoParse.initializeFields Word64.concrete ByteAuth.concrete 255 p.tag state.parser.fields else state.parser.fields) at h
  rw [hfields] at h
  exact h

#print axioms actual_group_end_rejection_step
#print axioms actual_top_end_rejection_step
end FullParserV3.Observed
