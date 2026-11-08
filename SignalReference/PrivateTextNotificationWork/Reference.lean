import PrivateVarintSemanticsWork.Reference64
import TlsMpc.Signal.PrivateTextNotificationContentSemantics

namespace LibSignalReference.Candidate.PrivateTextNotification
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
open LibSignalReference.Candidate.ProstEncoding
open LibSignalReference.Candidate.PrivateVarint

/-- No canonical-width input/precondition. Actual pinned prost encode_varint
writes exactly the timestamp bytes appended by the private field builder. -/
theorem timestampField_actual_append (value : U64) (buf : alloc.vec.Vec U8)
    (hsize : buf.length+10≤Usize.max) :
    ∃ after, _root_.ProstEncoding.encoding.varint.encode_varint vecDictionary value buf=.ok after ∧
      PrivateSend.join ByteAuth.concrete 11 [PrivateSend.literal ByteAuth.concrete 11 [56],
        PrivateVarint.uint64 Varint64.concrete ByteAuth.concrete value.bv]=
      PrivateBuffer.ofContents 11 (56 :: (vecContents after).drop (vecContents buf).length) := by
  obtain ⟨width,hw,hl,canonical⟩ := canonical_uint64_exists value.bv
  obtain ⟨after,ha,hv⟩ := vec_encode_appends value buf hsize
  refine ⟨after,ha,?_⟩
  rw [Signal.PrivateTextNotification.timestampField_contents value.bv width hw hl canonical,hv,List.drop_left]
  have enc := encode_publicNat64 value.bv width hw hl canonical
  simpa only [UScalar.bv_toNat] using congrArg (fun xs => PrivateBuffer.ofContents 11 (56::xs)) enc

/-- Exact nested Content/DataMessage/padding bytes with the timestamp bytes from
actual prost, for all uint64 values. UTF8 and actual app-derive/source agreement
are separate obligations; the body argument is a canonical private byte record. -/
theorem padded_content_actual_timestamp (body : List (BitVec 8)) (fits : body.length≤48)
    (value : U64) (buf : alloc.vec.Vec U8) (hsize : buf.length+10≤Usize.max) :
    ∃ after, _root_.ProstEncoding.encoding.varint.encode_varint vecDictionary value buf=.ok after ∧
      let dm := [10,BitVec.ofNat 8 body.length]++body++56::(vecContents after).drop (vecContents buf).length
      PrivateSend.join ByteAuth.concrete 80
        [PrivateProtobuf.bytesField Sha256.concrete ByteAuth.concrete 10
          (Signal.PrivateTextNotification.encodedDataMessage (PrivateBuffer.ofContents 48 body) value.bv),
         PrivateSend.literal ByteAuth.concrete 80 [128]]=
      PrivateBuffer.ofContents 80 (([10,BitVec.ofNat 8 dm.length]++dm)++[128]) := by
  obtain ⟨width,hw,hl,canonical⟩ := canonical_uint64_exists value.bv
  obtain ⟨after,ha,hv⟩ := vec_encode_appends value buf hsize
  refine ⟨after,ha,?_⟩
  rw [Signal.PrivateTextNotification.padded_content_contents body fits value.bv width hw hl canonical]
  have enc : Varint64.encode Varint64.concrete ByteAuth.concrete value.bv width=
      Varint.publicNat ByteAuth.concrete value.val := by
    simpa only [UScalar.bv_toNat] using encode_publicNat64 value.bv width hw hl canonical
  simp only [hv,List.drop_left,Signal.PrivateTextNotification.dataMessageBytes,enc]
end LibSignalReference.Candidate.PrivateTextNotification
