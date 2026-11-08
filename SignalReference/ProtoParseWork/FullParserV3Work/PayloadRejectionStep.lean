import ProtoParseWork.FullParserV3Work.RejectionState
import ProtoParseWork.FullParserV3Work.PayloadErrorProjection
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3.Observed
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 3000000

/-- Full actual payload-varint rejection observation. Valid known-wire and
budget decisions are explicit branch obligations; the decoder, suffix, record
mutation, constructor/parameter and remaining-scan freeze are proved here. -/
theorem actual_payload_rejection_step (bytes middle after : Slice U8) (position : Nat) (tag : U32)
    (kind : LoopSupportSkip.encoding.wire_type.WireType) (error : LoopSupportSkip.error.DecodeError)
    (state : State (BitVec 8) (BitVec 64))
    (hp : position < bytes.length) (hcap : bytes.length ≤ 512)
    (hs : state.parser.ok = 255) (hn : state.parser.next = BitVec.ofNat 64 position)
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,kind),middle))
    (hd : LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (.Err error,after))
    (hkind : kind = .Varint ∨ kind = .LengthDelimited) (hdepth : state.parser.depth.toNat ≤ 99)
    (hknown : validKnownMask ((rowsOf bytes)[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩) state.parser = 255) :
    ∀ positions : List Nat,
      let result := finish Word64.concrete ByteAuth.concrete
        (positions.foldl (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes))
          (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes) state position))
      result.parser.ok = 0 ∧ after = drop bytes result.parser.next.toNat ∧ result.parser.next.toNat ≤ bytes.length ∧
      result.parser.depth = state.parser.depth ∧ result.parser.stack = state.parser.stack ∧
      result.parser.fields = (if state.parser.depth = 0 then ProtoParse.initializeFields Word64.concrete ByteAuth.concrete
        255 (BitVec.ofNat 64 tag.val) state.parser.fields else state.parser.fields) ∧
      statusView (.Err (SignalMessageIntegration.skipError error)) = some result.error := by
  let rows := rowsOf bytes
  let key := rows[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩
  let payload := ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete key.stop (position+1) ((rows.drop (position+1)).take 10)
  let lastClear := (rows[bytes.length-1]?.getD ⟨0,BitVec.ofNat 64 (bytes.length-1),0⟩).ok
  let p := ProtoParse.planWithCursor Word64.concrete ByteAuth.concrete bytes.length position lastClear key payload state.parser
  obtain ⟨_,_,_,_,_,hkok,_,hkrange,hknz,htag,hwire,_⟩ := actual_key_row bytes middle position tag kind hp hk
  have hwire' : key.value &&& 7 = 0 ∨ key.value &&& 7 = 2 := by
    rcases hkind with rfl | rfl
    · exact Or.inl hwire
    · exact Or.inr hwire
  have hpay : payload.ok = 0 := actual_payload_error_mask bytes middle after position tag kind error hp hcap hk hd
  have hclass : classify Word64.concrete ByteAuth.concrete key payload state.parser = ⟨1,0⟩ :=
    classify_payload_varint_error key payload state.parser hkok hkrange hknz hwire' hdepth hknown hpay
  have hplan := actual_payload_failure_cursor bytes middle after position tag kind error state.parser hp hcap hk hd hkind hdepth hknown
  have hp0 : p.ok = 0 := hplan.1
  have ht : p.tag = BitVec.ofNat 64 tag.val := hplan.2.1.trans htag
  have hnumeric := apply_reject_any position p state.parser hs hn hp0
  have hparser : (step Word64.concrete ByteAuth.concrete bytes.length rows state position).parser =
      ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state.parser := rfl
  have herror : (step Word64.concrete ByteAuth.concrete bytes.length rows state position).error = ⟨1,0⟩ :=
    (step_rejection_error bytes.length position rows state hs hn hp0).trans hclass
  have herr : error = invalidError := by
    obtain ⟨r,remaining,hr,hpost,_⟩ := decode_full_reference middle
    rw [hd] at hr
    cases hr
    exact hpost.1
  have hm : statusView (.Err (SignalMessageIntegration.skipError error)) = some (⟨1,0⟩ : ErrorMeta (BitVec 64)) := by rw [herr]; rfl
  intro positions
  dsimp only
  rw [scan_failed bytes.length positions rows _ (by rw [hparser]; exact hnumeric.1),
    finish_failed _ (by rw [hparser]; exact hnumeric.1)]
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hparser]; exact hnumeric.1
  · rw [hparser,hnumeric.2.1]; exact hplan.2.2.1
  · rw [hparser,hnumeric.2.1]; exact hplan.2.2.2
  · rw [hparser]; exact hnumeric.2.2.1
  · rw [hparser]; exact hnumeric.2.2.2.1
  · rw [hparser,hnumeric.2.2.2.2,ht]
  · rw [herror]; exact hm

#print axioms actual_payload_rejection_step
end FullParserV3.Observed
