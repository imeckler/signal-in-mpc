import ProtoParseWork.FullParserV3Work.WrongWireDispatch
import ProtoParseWork.FullParserV3Work.FrozenRejection
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3.Observed
open SignalMessageIntegration DispatcherIntegration
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 3000000

private theorem wire_valid (kind : LoopSupportSkip.encoding.wire_type.WireType) :
    (BitVec.ofNat 64 (LibSignalReference.Candidate.ProstSkipKey.wireNumber kind)).toNat ≤ 5 := by
  cases kind <;> decide

private theorem wrong_classification (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hk : key.ok = 255)
    (hr : key.value.toNat ≤ 4294967295) (hn : key.value >>> 3 ≠ 0)
    (hw : (key.value &&& 7).toNat ≤ 5) (hv : validKnownMask key state = 0) :
    classify Word64.concrete ByteAuth.concrete key payload state = ⟨5,wirePair key⟩ :=
  (classify_valid_header key payload state hk hr hn hw).trans (field_classify_wrong_wire key payload state hv)

private theorem wrong_plan_facts (capacity position : Nat) (last : BitVec 8)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hk : key.ok = 255)
    (hv : validKnownMask key state = 0) (hm : (keyFields Word64.concrete ByteAuth.concrete key).ok = 255) :
    let p := ProtoParse.planWithCursor Word64.concrete ByteAuth.concrete capacity position last key payload state
    p.ok = 0 ∧ p.stop = key.stop ∧ p.tag = key.value >>> 3 := by
  have hb := plan_wrong_wire capacity key payload state hv
  refine ⟨hb,nonpayload_failure_stop capacity position last key payload state hk hb
    (nonpayload_mask key state (Or.inl hv)),plan_valid_tag capacity position last key payload state hm⟩

private theorem bounded_cursor_nat (cursor capacity : Nat) (hc : cursor ≤ capacity) (hcap : capacity ≤ 512) :
    (BitVec.ofNat 64 cursor).toNat = cursor := by
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]

#print axioms bounded_cursor_nat

/-- Numeric wrong-wire transition with a decoded actual key and an exact
constructor/parameter projection; concrete scalar/bytes callers supply both. -/
theorem wrong_wire_facts (bytes middle : Slice U8) (position : Nat) (tag : U32)
    (kind : LoopSupportSkip.encoding.wire_type.WireType) (error : prost.error.DecodeError)
    (state : State (BitVec 8) (BitVec 64)) (hp : position < bytes.length) (hcap : bytes.length ≤ 512)
    (hs : state.parser.ok = 255) (hn : state.parser.next = BitVec.ofNat 64 position)
    (hd : state.parser.depth = 0)
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,kind),middle))
    (hv : validKnownMask ((rowsOf bytes)[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩) state.parser = 0)
    (he : statusView (.Err error) = some ⟨5,wirePair ((rowsOf bytes)[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩)⟩) :
    (planOf bytes position state.parser).ok = 0 ∧
    middle = drop bytes (planOf bytes position state.parser).stop.toNat ∧
    (planOf bytes position state.parser).stop.toNat ≤ bytes.length ∧
    statusView (.Err error) = some (classifiedAt bytes position state.parser) ∧
    (planOf bytes position state.parser).tag = BitVec.ofNat 64 tag.val := by
  let key := (rowsOf bytes)[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩
  let payload := ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete key.stop (position+1) (((rowsOf bytes).drop (position+1)).take 10)
  let p := planOf bytes position state.parser
  classical
  let kr := actual_key_row bytes middle position tag kind hp hk
  let kc := Classical.choose kr
  have facts := Classical.choose_spec kr
  have hkb := facts.2.2.1
  have hrest := facts.2.2.2.1
  have hkok := facts.2.2.2.2.1
  have hkstop := facts.2.2.2.2.2.1
  have hkrange := facts.2.2.2.2.2.2.1
  have hknz := facts.2.2.2.2.2.2.2.1
  have htag := facts.2.2.2.2.2.2.2.2.1
  have hkind := facts.2.2.2.2.2.2.2.2.2.1
  have hkmask := facts.2.2.2.2.2.2.2.2.2.2
  obtain ⟨hp0,hstop,hptagKey⟩ := wrong_plan_facts bytes.length position
    ((rowsOf bytes)[bytes.length-1]?.getD ⟨0,BitVec.ofNat 64 (bytes.length-1),0⟩).ok key payload state.parser hkok hv hkmask
  change p.ok = 0 at hp0
  change p.stop = key.stop at hstop
  change p.tag = key.value >>> 3 at hptagKey
  have hstart : key.stop.toNat = position+kc := by rw [hkstop]; exact bounded_cursor_nat _ _ hkb hcap
  have ha : middle = drop bytes p.stop.toNat := by rw [hstop,hstart]; exact hrest
  have hb : p.stop.toNat ≤ bytes.length := by rw [hstop,hstart]; exact hkb
  have hvalid : (key.value &&& 7).toNat ≤ 5 := by rw [hkind]; exact wire_valid kind
  have hm : statusView (.Err error) = some (classifiedAt bytes position state.parser) :=
    he.trans (congrArg some (wrong_classification key payload state.parser hkok hkrange hknz hvalid hv)).symm
  have hptag : p.tag = BitVec.ofNat 64 tag.val := hptagKey.trans htag
  exact ⟨hp0,ha,hb,hm,hptag⟩


#print axioms wrong_wire_facts
end FullParserV3.Observed
