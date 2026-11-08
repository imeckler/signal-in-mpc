import ProtoParseWork.FullParserV3Work.TopLeafState
import ProtoParseWork.FullParserV3Work.KnownDispatchSuccess
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open LibSignalReference.Candidate.ProstSkipSlice LibSignalReference.Candidate.ProstSkipBuf
open LibSignalReference.Candidate.ProstTopField LibSignalReference.Candidate.ProstSkipKey
open LibSignalReference.Candidate.ProstSkipPlan
set_option maxHeartbeats 3000000

/-- Every actual successful top-level counter/previous-counter parse agrees
with the full numeric scan and six-field message projection, including uint64
to uint32 truncation and duplicate replacement. -/
theorem top_scalar_scan (bytes middle after : Slice U8) (position : Nat) (tag : U32) (value : U64)
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hpos : position < bytes.length) (hcap : bytes.length ≤ 512)
    (hat : StateAt bytes position state []) (ht : ScalarTag tag)
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,.Varint),middle))
    (hv : LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (.Ok value,after)) :
    ∃ finish, position < finish ∧ finish ≤ bytes.length ∧ after = drop bytes finish ∧
      let result := stepOf bytes state position
      ∃ hfinal : StateAt bytes finish result [], scanOf bytes position finish state = result ∧
        messageView bytes result.fields hfinal.fields_size = setScalar tag (UScalar.cast .U32 value)
          (messageView bytes state.fields hat.fields_size) := by
  dsimp only
  let rows := ProtoParse.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes)
  let key := rows[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩
  have keyData : ∃ count, 1 ≤ count ∧ count ≤ 10 ∧ position+count ≤ bytes.length ∧
      middle = drop bytes (position+count) ∧ key.ok = 255 ∧
      key.stop = BitVec.ofNat 64 (position+count) ∧ key.value.toNat ≤ 4294967295 ∧ key.value >>> 3 ≠ 0 ∧
      key.value >>> 3 = BitVec.ofNat 64 tag.val ∧ key.value &&& 7 = 0 ∧
      (keyFields Word64.concrete ByteAuth.concrete key).ok = 255 := actual_key_row bytes middle position tag .Varint hpos hk
  obtain ⟨kc,hk1,hk10,hkb,hrest,hkok,hkstop,hkrange,hknz,htag,hkind,hkmask⟩ := keyData
  have hnonempty : 0 < middle.length := by
    obtain ⟨r,rest,hr,_,hlt⟩ := varint_total middle
    rw [hv] at hr
    cases hr
    have h := hlt value rfl
    omega
  have hstart : position+kc < bytes.length := by rw [hrest,drop_length] at hnonempty; omega
  have hv' : LoopSupportSkip.encoding.varint.decode_varint sliceBuf (drop bytes (position+kc)) = .ok (.Ok value,after) := by simpa only [hrest] using hv
  obtain ⟨pc,hp1,_,hpb,hafter,hpayload⟩ := payload_actual_success bytes after position kc value hk1 hk10 hstart (by omega) hv'
  let payload := ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete key.stop (position+1) ((rows.drop (position+1)).take 10)
  have hpay : payload = ⟨255,BitVec.ofNat 64 (position+kc+pc),value.bv⟩ := by
    dsimp only [payload]
    rw [hkstop]
    exact hpayload
  let p := ProtoParse.plan Word64.concrete ByteAuth.concrete bytes.length key payload state
  have hdepth : state.depth = 0 := hat.frames.depth_eq
  have hscalar : key.value >>> 3 = 2 ∨ key.value >>> 3 = 3 := by
    rcases ht with rfl | rfl <;> rw [htag] <;> decide
  have hgood : p.ok = 255 := by
    rw [scalar_top_mask bytes.length key payload state hkok hkrange hdepth hscalar hkind,hpay]
  have hstop : p.stop = BitVec.ofNat 64 (position+kc+pc) := by
    rw [varint_stop bytes.length key payload state hkind,hpay]
  have hpkind : p.kind = 0 := hkind
  have hptag : p.tag = BitVec.ofNat 64 tag.val := htag
  have hstep : stepOf bytes state position = ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state := by
    change ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position
      (ProtoParse.planWithCursor Word64.concrete ByteAuth.concrete bytes.length position _ key payload state) state = _
    rw [successful_plan _ _ _ _ _ _ hkmask hgood]
  obtain ⟨hfinal,hscan⟩ := package_top_step bytes position (position+kc+pc) state p hat hgood
    (by rw [hpkind]; decide) (by rw [hpkind]; decide) hstop hstep (by omega) hpb hcap
  refine ⟨position+kc+pc,by omega,hpb,hafter,hfinal,hscan,?_⟩
  calc
    messageView bytes (stepOf bytes state position).fields hfinal.fields_size =
        replaceMessage bytes p.tag p.payload (messageView bytes state.fields hat.fields_size) := by
      simpa only [hstep] using apply_top_success_view bytes state position p hat.fields_size hat.ok hat.cursor hdepth hgood
    _ = _ := by
      change replaceMessage bytes p.tag payload _ = _
      rw [hptag,hpay]
      exact scalar_replace_view bytes tag value _ _ ht

#print axioms top_scalar_scan
end FullParserV3
