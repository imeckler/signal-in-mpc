import ProtoParseWork.FullParserV3Work.FrozenRejection
import ProtoParseWork.FullParserV3Work.NestedFixedScan
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open SignalMessageIntegration DispatcherIntegration
open LoopSupportSkip LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkip
open LibSignalReference.Candidate.ProstSkipKey LibSignalReference.Candidate.ProstSkipPlan LibSignalReference.Candidate.ProstTopField
set_option maxHeartbeats 4000000

private theorem fixed_actual_rule (kind : encoding.wire_type.WireType) (width : Nat) (tag count : U32)
    (before : Slice U8) (hw : FixedWidth kind width) (hc : count ≠ 0#u32) :
    encoding.skip_field sliceBuf kind tag before ⟨count⟩ = .ok (fixedResult before width) := by
  rcases hw with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact fixed64_reference _ _ _ hc
  · exact fixed32_reference _ _ _ hc

private theorem fixed_numeric_rule (capacity : Nat) (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (kind : encoding.wire_type.WireType) (width : Nat)
    (hw : FixedWidth kind width) (hk : key.ok = 255) (hr : key.value.toNat ≤ 4294967295)
    (ht : key.value >>> 3 ≠ 0) (hkind : key.value &&& 7 = BitVec.ofNat 64 (wireNumber kind))
    (hd : state.depth.toNat ≤ 99) (hskip : state.depth ≠ 0 ∨ 6 < (key.value >>> 3).toNat) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok =
      Word64.concrete.ule (key.stop+BitVec.ofNat 64 width) (BitVec.ofNat 64 capacity) := by
  by_cases hz : state.depth = 0
  · have hu := hskip.resolve_left (not_not.mpr hz)
    rcases hw with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact fixed64_unknown_top _ _ _ _ hk hr ht hkind hz hu
    · exact fixed32_unknown_top _ _ _ _ hk hr ht hkind hz hu
  · rcases hw with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact fixed64_in_group _ _ _ _ hk hr ht hkind hz hd
    · exact fixed32_in_group _ _ _ _ hk hr ht hkind hz hd

namespace Observed

/-- Actual fixed32/fixed64 underflow preserves the full record/frames, consumes
only its key, and freezes exact BufferUnderflow metadata through the rest of the
scan. Count-zero recursion failure is handled separately, not conflated here. -/
theorem actual_fixed_rejection_step (bytes middle after : Slice U8) (position : Nat) (tag count : U32)
    (kind : encoding.wire_type.WireType) (width : Nat) (hw : FixedWidth kind width)
    (error : LoopSupportSkip.error.DecodeError) (state : State (BitVec 8) (BitVec 64))
    (hp : position < bytes.length) (hcap : bytes.length ≤ 512)
    (hs : state.parser.ok = 255) (hn : state.parser.next = BitVec.ofNat 64 position)
    (hl : state.parser.fields.length = 6) (hdepth : state.parser.depth.toNat ≤ 99) (hc : count ≠ 0#u32)
    (hallowed : state.parser.depth ≠ 0 ∨ 6 < (((rowsOf bytes)[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩).value >>> 3).toNat)
    (hk : encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,kind),middle))
    (hskip : encoding.skip_field sliceBuf kind tag middle ⟨count⟩ = .ok (.Err error,after)) :
    ∀ positions : List Nat, ActiveRejection bytes after (skipError error) state
      (finish Word64.concrete ByteAuth.concrete (positions.foldl (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes))
        (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes) state position))) state.parser.fields := by
  let key := (rowsOf bytes)[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩
  let payload := ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete key.stop (position+1) (((rowsOf bytes).drop (position+1)).take 10)
  let p := planOf bytes position state.parser
  obtain ⟨kc,_,_,hkb,hrest,hkok,hkstop,hkrange,hknz,_,hkind,hkmask⟩ := actual_key_row bytes middle position tag kind hp hk
  rw [fixed_actual_rule kind width tag count middle hw hc] at hskip
  have hshort : middle.length < width := by
    by_contra h
    simp only [fixedResult,if_neg h] at hskip
    cases hskip
  simp only [fixedResult,if_pos hshort] at hskip
  have herr : error = decodeError .BufferUnderflow := (core.result.Result.Err.inj (congrArg Prod.fst (Result.ok.inj hskip))).symm
  have hafter : after = middle := (congrArg Prod.snd (Result.ok.inj hskip)).symm
  have hstart : key.stop.toNat = position+kc := by rw [hkstop,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have hwidth : width ≤ 8 := by rcases hw with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> decide
  have hbad : (ProtoParse.plan Word64.concrete ByteAuth.concrete bytes.length key payload state.parser).ok = 0 := by
    rw [fixed_numeric_rule bytes.length key payload state.parser kind width hw hkok hkrange hknz hkind hdepth hallowed,
      fixed_bounds key.stop bytes.length width (by omega) hcap hwidth]
    rw [hrest,drop_length] at hshort
    rw [if_neg (by rw [hstart]; omega)]
  have hkind' : key.value &&& 7 = 1 ∨ key.value &&& 7 = 5 := by
    rcases hw with ⟨rfl,_⟩ | ⟨rfl,_⟩
    · exact Or.inl hkind
    · exact Or.inr hkind
  have h0 : key.value &&& 7 ≠ 0 := by rcases hkind' with h | h <;> rw [h] <;> decide
  have h2 : key.value &&& 7 ≠ 2 := by rcases hkind' with h | h <;> rw [h] <;> decide
  have hp0 : p.ok = 0 := hbad
  have hstop : p.stop = key.stop := nonpayload_failure_stop _ _ _ key payload state.parser hkok hbad
    (nonpayload_mask key state.parser (Or.inr (Or.inr ⟨h0,h2⟩)))
  have htag : p.tag = key.value >>> 3 := plan_valid_tag _ _ _ _ _ _ hkmask
  have ha : after = drop bytes p.stop.toNat := by rw [hstop,hstart,hafter]; exact hrest
  have hb : p.stop.toNat ≤ bytes.length := by rw [hstop,hstart]; exact hkb
  have hvalid : (key.value &&& 7).toNat ≤ 5 := by rcases hkind' with h | h <;> rw [h] <;> decide
  have hm : statusView (.Err (skipError error)) = some (classifiedAt bytes position state.parser) := by
    change statusView (.Err (skipError error)) = some (classify Word64.concrete ByteAuth.concrete key payload state.parser)
    rw [classify_valid_header key payload state.parser hkok hkrange hknz hvalid,
      field_classify_known_wire key payload state.parser (valid_known_skip key state.parser hallowed),
      skip_code_fixed key payload state.parser hkind' hdepth,herr]
    rfl
  have hfields : (if state.parser.depth = 0 then ProtoParse.initializeFields Word64.concrete ByteAuth.concrete 255 p.tag state.parser.fields else state.parser.fields) = state.parser.fields := by
    by_cases hz : state.parser.depth = 0
    · rw [if_pos hz]
      apply initialize_unknown state.parser.fields p.tag (by omega)
      rw [htag]
      exact hallowed.resolve_left (not_not.mpr hz)
    · rw [if_neg hz]
  intro positions
  have h := freeze_active_reject bytes after position (skipError error) state hs hn hp0 ha hb hm positions
  change ActiveRejection bytes after (skipError error) state _
    (if state.parser.depth = 0 then ProtoParse.initializeFields Word64.concrete ByteAuth.concrete 255 p.tag state.parser.fields else state.parser.fields) at h
  rw [hfields] at h
  exact h

#print axioms actual_fixed_rejection_step
end Observed
end FullParserV3
