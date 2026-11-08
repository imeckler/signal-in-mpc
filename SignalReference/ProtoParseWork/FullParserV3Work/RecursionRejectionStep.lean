import ProtoParseWork.FullParserV3Work.FrozenRejection
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open SignalMessageIntegration DispatcherIntegration
open LoopSupportSkip LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkip
open LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 3000000

private theorem plan_recursion_limit (capacity : Nat) (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hd : 99 < state.depth.toNat) (h4 : key.value &&& 7 ≠ 4) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok = 0 := by
  have hb : Word64.concrete.ule state.depth (Word64.concrete.const 99) = 0 := by rw [Word64.ule_value]; exact if_neg (by change ¬state.depth.toNat ≤ 99; omega)
  have he : Word64.eq Word64.concrete ByteAuth.concrete (Word64.concrete.band key.value (Word64.concrete.const 7)) (Word64.concrete.const 4) = 0 := by rw [word_eq_value]; exact if_neg h4
  have hz (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  have hz' (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  simp only [ProtoParse.plan,hb,he,hz,hz',Word64.bor,show ByteAuth.concrete.xor 0 0 = 0 from rfl]

namespace Observed

/-- The actual budget-zero child failure agrees with depth100 rejection before
any payload attempt. EndGroup is excluded by the actual group loop's earlier
closing check; matching depth100 closes are covered by group_end_scan. -/
theorem actual_recursion_rejection_step (bytes middle after : Slice U8) (position : Nat) (tag : U32)
    (kind : encoding.wire_type.WireType) (hkind : kind ≠ .EndGroup)
    (error : LoopSupportSkip.error.DecodeError) (state : State (BitVec 8) (BitVec 64))
    (hp : position < bytes.length) (hcap : bytes.length ≤ 512)
    (hs : state.parser.ok = 255) (hn : state.parser.next = BitVec.ofNat 64 position)
    (hdepth : state.parser.depth.toNat = 100)
    (hk : encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,kind),middle))
    (hskip : encoding.skip_field sliceBuf kind tag middle ⟨0#u32⟩ = .ok (.Err error,after)) :
    ∀ positions : List Nat, ActiveRejection bytes after (skipError error) state
      (finish Word64.concrete ByteAuth.concrete (positions.foldl (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes))
        (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes) state position))) state.parser.fields := by
  let key := (rowsOf bytes)[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩
  let payload := ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete key.stop (position+1) (((rowsOf bytes).drop (position+1)).take 10)
  let p := planOf bytes position state.parser
  obtain ⟨kc,_,_,hkb,hrest,hkok,hkstop,hkrange,hknz,_,hwire,hkmask⟩ := actual_key_row bytes middle position tag kind hp hk
  rw [recursion_limit_first] at hskip
  have herr : error = decodeError .RecursionLimitReached := (core.result.Result.Err.inj (congrArg Prod.fst (Result.ok.inj hskip))).symm
  have hafter : after = middle := (congrArg Prod.snd (Result.ok.inj hskip)).symm
  have hd : state.parser.depth ≠ 0 := by intro hz; rw [hz] at hdepth; change 0 = 100 at hdepth; omega
  have hg : 99 < state.parser.depth.toNat := by omega
  have h4 : key.value &&& 7 ≠ 4 := by
    rw [hwire]
    cases kind <;> simp_all [wireNumber]
    all_goals decide
  have hvalid : (key.value &&& 7).toNat ≤ 5 := by rw [hwire]; cases kind <;> decide
  have hbad := plan_recursion_limit bytes.length key payload state.parser hg h4
  have hp0 : p.ok = 0 := hbad
  have hstop : p.stop = key.stop := nonpayload_failure_stop _ _ _ key payload state.parser hkok hbad
    (nonpayload_mask key state.parser (Or.inr (Or.inl hg)))
  have hstart : key.stop.toNat = position+kc := by rw [hkstop,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have ha : after = drop bytes p.stop.toNat := by rw [hstop,hstart,hafter]; exact hrest
  have hb : p.stop.toNat ≤ bytes.length := by rw [hstop,hstart]; exact hkb
  have hm : statusView (.Err (skipError error)) = some (classifiedAt bytes position state.parser) := by
    change statusView (.Err (skipError error)) = some (classify Word64.concrete ByteAuth.concrete key payload state.parser)
    rw [classify_valid_header key payload state.parser hkok hkrange hknz hvalid,
      field_classify_known_wire key payload state.parser (valid_known_skip key state.parser (Or.inl hd)),
      skip_code_recursion key payload state.parser h4 hg,herr]
    rfl
  intro positions
  have h := freeze_active_reject bytes after position (skipError error) state hs hn hp0 ha hb hm positions
  simpa only [if_neg hd] using h

#print axioms actual_recursion_rejection_step
end Observed
end FullParserV3
