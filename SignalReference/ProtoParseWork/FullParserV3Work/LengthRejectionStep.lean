import ProtoParseWork.FullParserV3Work.LengthFailurePlan
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3.Observed
open SignalMessageIntegration DispatcherIntegration
open LoopSupportSkip LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkip
open LibSignalReference.Candidate.ProstSkipKey LibSignalReference.Candidate.ProstSkipPlan LibSignalReference.Candidate.ProstTopField
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

/-- Actual length-delimited underflow consumes the length varint, retains the
existing/default Option rather than writing a partial value, and preserves
BufferUnderflow through finish even inside an unclosed group at EOF. -/
theorem actual_length_rejection_step (bytes middle rest after : Slice U8) (position : Nat) (tag count : U32) (value : U64)
    (error : LoopSupportSkip.error.DecodeError) (state : State (BitVec 8) (BitVec 64))
    (hp : position < bytes.length) (hcap : bytes.length ≤ 512)
    (hs : state.parser.ok = 255) (hn : state.parser.next = BitVec.ofNat 64 position)
    (hdepth : state.parser.depth.toNat ≤ 99) (hc : count ≠ 0#u32)
    (hknown : validKnownMask ((rowsOf bytes)[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩) state.parser = 255)
    (hk : encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,.LengthDelimited),middle))
    (hv : encoding.varint.decode_varint sliceBuf middle = .ok (.Ok value,rest))
    (hskip : encoding.skip_field sliceBuf .LengthDelimited tag middle ⟨count⟩ = .ok (.Err error,after)) :
    ∀ positions : List Nat, ActiveRejection bytes after (skipError error) state
      (finish Word64.concrete ByteAuth.concrete (positions.foldl (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes))
        (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes) state position)))
      (if state.parser.depth = 0 then ProtoParse.initializeFields Word64.concrete ByteAuth.concrete
        255 (BitVec.ofNat 64 tag.val) state.parser.fields else state.parser.fields) := by
  let key := (rowsOf bytes)[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩
  let payload := ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete key.stop (position+1) (((rowsOf bytes).drop (position+1)).take 10)
  let p := planOf bytes position state.parser
  obtain ⟨kc,h1,h10,hkb,hmiddle,hkok,hkstop,hkrange,hknz,htag,hkind,hkmask⟩ := actual_key_row bytes middle position tag .LengthDelimited hp hk
  have hkind2 : key.value &&& 7 = 2 := hkind
  rw [length_delimited_after middle rest value tag count hc hv] at hskip
  have hshort : rest.length < value.val := by
    by_contra h
    simp only [fixedResult,if_neg h] at hskip
    cases hskip
  simp only [fixedResult,if_pos hshort] at hskip
  have herr : error = decodeError .BufferUnderflow := (core.result.Result.Err.inj (congrArg Prod.fst (Result.ok.inj hskip))).symm
  have hafter : after = rest := (congrArg Prod.snd (Result.ok.inj hskip)).symm
  have hnempty := varint_success_decreases middle rest value hv
  have hstart : position+kc < bytes.length := by rw [hmiddle,drop_length] at hnempty; omega
  have hv' : encoding.varint.decode_varint sliceBuf (drop bytes (position+kc)) = .ok (.Ok value,rest) := by simpa only [hmiddle] using hv
  obtain ⟨pc,_,_,hpb,hrest,hpay'⟩ := payload_actual_success bytes rest position kc value h1 h10 hstart (by omega) hv'
  have hpay : payload = ⟨255,BitVec.ofNat 64 (position+kc+pc),value.bv⟩ := by dsimp only [payload]; rw [hkstop]; exact hpay'
  have hpayNat : payload.stop.toNat = position+kc+pc := by rw [hpay]; exact Nat.mod_eq_of_lt (by omega)
  have hpayOK : payload.ok = 255 := by rw [hpay]
  have hfit : Word64.concrete.ule payload.value (Word64.concrete.sub (Word64.concrete.const bytes.length) payload.stop) = 0 := by
    change Word64.concrete.ule payload.value (BitVec.ofNat 64 bytes.length - payload.stop) = 0
    rw [length_bounds payload.stop payload.value bytes.length (by omega) hcap,hpayNat]
    have hn : ¬payload.value.toNat ≤ bytes.length-(position+kc+pc) := by
      rw [hpay]
      change ¬value.bv.toNat ≤ bytes.length-(position+kc+pc)
      rw [UScalar.bv_toNat]
      rw [hrest,drop_length] at hshort
      omega
    exact if_neg hn
  have hbad := plan_length_invalid bytes.length key payload state.parser hkind2 hfit
  have hp0 : p.ok = 0 := hbad
  have hattempt := payload_attempt_mask key state.parser hkmask hknown hdepth (Or.inr hkind2)
  have hstop : p.stop = payload.stop := payload_decoded_failure_stop _ _ _ key payload state.parser hbad hattempt hpayOK
  have hptag : p.tag = BitVec.ofNat 64 tag.val := (plan_valid_tag _ _ _ _ _ _ hkmask).trans htag
  have ha : after = drop bytes p.stop.toNat := by rw [hstop,hpayNat,hafter]; exact hrest
  have hb : p.stop.toNat ≤ bytes.length := by rw [hstop,hpayNat]; exact hpb
  have hvalid : (key.value &&& 7).toNat ≤ 5 := by rw [hkind2]; decide
  have hm : statusView (.Err (skipError error)) = some (classifiedAt bytes position state.parser) := by
    change statusView (.Err (skipError error)) = some (classify Word64.concrete ByteAuth.concrete key payload state.parser)
    rw [classify_valid_header key payload state.parser hkok hkrange hknz hvalid,
      field_classify_known_wire key payload state.parser hknown,
      skip_code_length_underflow key payload state.parser hkind2 hdepth hpayOK,herr]
    rfl
  intro positions
  have h := freeze_active_reject bytes after position (skipError error) state hs hn hp0 ha hb hm positions
  change ActiveRejection bytes after (skipError error) state _
    (if state.parser.depth = 0 then ProtoParse.initializeFields Word64.concrete ByteAuth.concrete 255 p.tag state.parser.fields else state.parser.fields) at h
  rw [hptag] at h
  exact h

#print axioms actual_length_rejection_step
end FullParserV3.Observed
