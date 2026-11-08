import ProtoParseWork.FullParserV3Work.TopScalarScan
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open LibSignalReference.Candidate.ProstSkipSlice LibSignalReference.Candidate.ProstSkipBuf
open LibSignalReference.Candidate.ProstTopField LibSignalReference.Candidate.ProstSkipKey
open LibSignalReference.Candidate.ProstSkipPlan
set_option maxHeartbeats 3000000

/-- Every supported actual top-level bytes replacement agrees with the whole
numeric interval and all six projected fields, including duplicates and empty
vectors. Decoder and data suffixes are both retained. -/
theorem top_bytes_scan (bytes middle payloadAfter after : Slice U8) (position : Nat) (tag : U32) (value : U64)
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hpos : position < bytes.length) (hcap : bytes.length ≤ 512)
    (hat : StateAt bytes position state []) (ht : BytesTag tag)
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,.LengthDelimited),middle))
    (hv : LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (.Ok value,payloadAfter))
    (hfit : value.val ≤ payloadAfter.length) (hfinal : after = drop payloadAfter value.val) :
    ∃ finish, position < finish ∧ finish ≤ bytes.length ∧ after = drop bytes finish ∧
      let result := stepOf bytes state position
      ∃ hresult : StateAt bytes finish result [], scanOf bytes position finish state = result ∧
        messageView bytes result.fields hresult.fields_size = setBytes tag
          (LibSignalReference.Candidate.ProstVecAdapter.fromSlice (ProstBytesCandidate.ContentModel.take payloadAfter value.val))
          (messageView bytes state.fields hat.fields_size) := by
  dsimp only
  let rows := ProtoParse.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes)
  let key := rows[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩
  have keyData : ∃ count, 1 ≤ count ∧ count ≤ 10 ∧ position+count ≤ bytes.length ∧
      middle = drop bytes (position+count) ∧ key.ok = 255 ∧
      key.stop = BitVec.ofNat 64 (position+count) ∧ key.value.toNat ≤ 4294967295 ∧ key.value >>> 3 ≠ 0 ∧
      key.value >>> 3 = BitVec.ofNat 64 tag.val ∧ key.value &&& 7 = 2 ∧
      (keyFields Word64.concrete ByteAuth.concrete key).ok = 255 := actual_key_row bytes middle position tag .LengthDelimited hpos hk
  obtain ⟨kc,hk1,hk10,hkb,hrest,hkok,hkstop,hkrange,hknz,htag,hkind,hkmask⟩ := keyData
  have hnonempty : 0 < middle.length := by
    obtain ⟨r,rest,hr,_,hlt⟩ := varint_total middle
    rw [hv] at hr
    cases hr
    have h := hlt value rfl
    omega
  have hstart : position+kc < bytes.length := by rw [hrest,drop_length] at hnonempty; omega
  have hv' : LoopSupportSkip.encoding.varint.decode_varint sliceBuf (drop bytes (position+kc)) = .ok (.Ok value,payloadAfter) := by simpa only [hrest] using hv
  obtain ⟨pc,hp1,_,hpb,hafter,hpayload⟩ := payload_actual_success bytes payloadAfter position kc value hk1 hk10 hstart (by omega) hv'
  let payload := ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete key.stop (position+1) ((rows.drop (position+1)).take 10)
  have hpay : payload = ⟨255,BitVec.ofNat 64 (position+kc+pc),value.bv⟩ := by
    dsimp only [payload]
    rw [hkstop]
    exact hpayload
  let p := ProtoParse.plan Word64.concrete ByteAuth.concrete bytes.length key payload state
  have hstartNat : (BitVec.ofNat 64 (position+kc+pc)).toNat = position+kc+pc := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have hfitAbs : value.val ≤ bytes.length-(position+kc+pc) := by rw [hafter,drop_length] at hfit; exact hfit
  have hbound : position+kc+pc+value.val ≤ bytes.length := by omega
  have hdepth : state.depth = 0 := hat.frames.depth_eq
  have hbytes : key.value >>> 3 = 1 ∨ key.value >>> 3 = 4 ∨ key.value >>> 3 = 5 ∨ key.value >>> 3 = 6 := by
    rcases ht with rfl | rfl | rfl | rfl <;> rw [htag] <;> decide
  have hgood : p.ok = 255 := by
    rw [bytes_top_mask bytes.length key payload state hkok hkrange hdepth hbytes hkind,hpay]
    change 255 &&& Word64.concrete.ule value.bv
      (BitVec.ofNat 64 bytes.length - BitVec.ofNat 64 (position+kc+pc)) = 255
    rw [length_bounds _ _ bytes.length (by rw [hstartNat]; omega) hcap]
    simp only [UScalar.bv_toNat,hstartNat,if_pos hfitAbs]
    rfl
  have hstop : p.stop = BitVec.ofNat 64 (position+kc+pc+value.val) := by
    rw [length_stop bytes.length key payload state hkind,hpay]
    have hb : value.val < 2^64 := by have h := value.bv.isLt; simpa only [UScalar.bv_toNat] using h
    have hval : value.bv = BitVec.ofNat 64 value.val := by
      apply BitVec.eq_of_toNat_eq
      simp only [UScalar.bv_toNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hb]
    change BitVec.ofNat 64 (position+kc+pc) + value.bv = _
    rw [hval]
    simp only [BitVec.ofNat_add]
  have hpkind : p.kind = 2 := hkind
  have hptag : p.tag = BitVec.ofNat 64 tag.val := htag
  have hstep : stepOf bytes state position = ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state := by
    change ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position
      (ProtoParse.planWithCursor Word64.concrete ByteAuth.concrete bytes.length position _ key payload state) state = _
    rw [successful_plan _ _ _ _ _ _ hkmask hgood]
  obtain ⟨hresult,hscan⟩ := package_top_step bytes position (position+kc+pc+value.val) state p hat hgood
    (by rw [hpkind]; decide) (by rw [hpkind]; decide) hstop hstep (by omega) hbound hcap
  refine ⟨position+kc+pc+value.val,by omega,hbound,?_,hresult,hscan,?_⟩
  · rw [hfinal,hafter,drop_add]
  · calc
      messageView bytes (stepOf bytes state position).fields hresult.fields_size =
          replaceMessage bytes p.tag p.payload (messageView bytes state.fields hat.fields_size) := by
        simpa only [hstep] using apply_top_success_view bytes state position p hat.fields_size hat.ok hat.cursor hdepth hgood
      _ = _ := by
        change replaceMessage bytes p.tag payload _ = _
        rw [hptag,hpay,bytes_replace_view bytes tag value (position+kc+pc) _ ht (by omega)]
        rw [hafter]
        rfl

#print axioms top_bytes_scan
end FullParserV3
