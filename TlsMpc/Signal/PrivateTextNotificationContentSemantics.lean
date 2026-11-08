import TlsMpc.Signal.PrivateProtobufShortSemantics
import TlsMpc.Signal.PrivateTextNotificationSemantics
import TlsMpc.Signal.PrivateVarintSemantics

/-! Canonical body/timestamp Content serialization. Canonical varint width is a
mathematical witness only; no width selector is an input to these circuits.
UTF8 language refinement and actual source/prost linkage remain separate. -/
namespace TlsMpc.Signal.PrivateTextNotification
open PrivateBuffer

theorem uint64_contents (word : BitVec 64) (width : Nat) (hw : 0<width) (hl : width≤10)
    (canonical : Varint64.canonicalGroups (Varint64.groups Varint64.concrete word) width) :
    PrivateVarint.uint64 Varint64.concrete ByteAuth.concrete word =
      ofContents 10 (Varint64.encode Varint64.concrete ByteAuth.concrete word width) := by
  have len : (Varint64.groups Varint64.concrete word).length=10 := by simp [Varint64.groups]
  have head : width=1 ∨ (Varint64.groups Varint64.concrete word)[width-1]?.getD 0≠0 := by
    rcases canonical.2 with h|h
    · exact Or.inl h
    · exact Or.inr h
  have h := PrivateVarint.fromGroups_canonical (Varint64.groups Varint64.concrete word) width
    hw (by omega) (by omega) (by simpa only [len] using canonical.1) head
  rw [PrivateVarint.canonical_data_bytes _ width (by omega)] at h
  simpa only [PrivateVarint.uint64,Varint64.encode,len,ofContents,Varint.encode_length,
    Varint64.encode_length,Varint.encodeGroups,List.length_map,List.length_range] using h

theorem timestampField_contents (word : BitVec 64) (width : Nat) (hw : 0<width) (hl : width≤10)
    (canonical : Varint64.canonicalGroups (Varint64.groups Varint64.concrete word) width) :
    PrivateSend.join ByteAuth.concrete 11 [PrivateSend.literal ByteAuth.concrete 11 [56],
      PrivateVarint.uint64 Varint64.concrete ByteAuth.concrete word]=
      ofContents 11 (56 :: Varint64.encode Varint64.concrete ByteAuth.concrete word width) := by
  rw [uint64_contents word width hw hl canonical]
  unfold PrivateSend.join PrivateSend.literal
  simp only [List.foldl_cons,List.foldl_nil]
  rw [fromPublic_contents 11 (by decide) [] (by simp),fromPublic_contents 11 (by decide) [56] (by simp)]
  rw [append_contents 11 11 11 (by decide) [] [56] (by simp)]
  simpa using append_contents 11 11 10 (by decide) [56]
    (Varint64.encode Varint64.concrete ByteAuth.concrete word width) (by simp [Varint64.encode_length];omega)

def dataMessageBytes (body : List (BitVec 8)) (word : BitVec 64) (width : Nat) : List (BitVec 8) :=
  [10,BitVec.ofNat 8 body.length] ++ body ++ 56 :: Varint64.encode Varint64.concrete ByteAuth.concrete word width

def encodedDataMessage (body : Buffer (BitVec 8)) (word : BitVec 64) : Buffer (BitVec 8) :=
  PrivateSend.join ByteAuth.concrete 63 [PrivateProtobuf.bytesField Sha256.concrete ByteAuth.concrete 10 body,
    PrivateSend.join ByteAuth.concrete 11 [PrivateSend.literal ByteAuth.concrete 11 [56],
      PrivateVarint.uint64 Varint64.concrete ByteAuth.concrete word]]

theorem dataMessage_contents (body : List (BitVec 8)) (fits : body.length≤48)
    (word : BitVec 64) (width : Nat) (hw : 0<width) (hl : width≤10)
    (canonical : Varint64.canonicalGroups (Varint64.groups Varint64.concrete word) width) :
    encodedDataMessage (ofContents 48 body) word=ofContents 63 (dataMessageBytes body word width) := by
  unfold encodedDataMessage
  rw [PrivateProtobuf.bytesField_short_contents 48 10 (by decide) body fits (by omega),
    timestampField_contents word width hw hl canonical]
  unfold PrivateSend.join
  simp only [List.foldl_cons,List.foldl_nil]
  rw [fromPublic_contents 63 (by decide) [] (by simp)]
  rw [append_contents 63 63 52 (by decide) [] ([BitVec.ofNat 8 10,BitVec.ofNat 8 body.length]++body) (by simp;omega)]
  simp only [List.nil_append]
  exact append_contents 63 63 11 (by decide) _ _ (by simp [Varint64.encode_length];omega)

theorem content_contents (body : List (BitVec 8)) (fits : body.length≤48)
    (word : BitVec 64) (width : Nat) (hw : 0<width) (hl : width≤10)
    (canonical : Varint64.canonicalGroups (Varint64.groups Varint64.concrete word) width) :
    PrivateProtobuf.bytesField Sha256.concrete ByteAuth.concrete 10
      (encodedDataMessage (ofContents 48 body) word)=
    ofContents 67 ([10,BitVec.ofNat 8 (dataMessageBytes body word width).length]++dataMessageBytes body word width) := by
  rw [dataMessage_contents body fits word width hw hl canonical]
  exact PrivateProtobuf.bytesField_short_contents 63 10 (by decide) _
    (by simp [dataMessageBytes,Varint64.encode_length];omega)
    (by simp [dataMessageBytes,Varint64.encode_length];omega)

theorem padded_content_contents (body : List (BitVec 8)) (fits : body.length≤48)
    (word : BitVec 64) (width : Nat) (hw : 0<width) (hl : width≤10)
    (canonical : Varint64.canonicalGroups (Varint64.groups Varint64.concrete word) width) :
    PrivateSend.join ByteAuth.concrete 80
      [PrivateProtobuf.bytesField Sha256.concrete ByteAuth.concrete 10
        (encodedDataMessage (ofContents 48 body) word),
       PrivateSend.literal ByteAuth.concrete 80 [128]] =
      ofContents 80 (([10,BitVec.ofNat 8 (dataMessageBytes body word width).length]++
        dataMessageBytes body word width)++[128]) := by
  rw [content_contents body fits word width hw hl canonical]
  exact iso7816_contents 67 _ (by simp [dataMessageBytes,Varint64.encode_length];omega)
end TlsMpc.Signal.PrivateTextNotification

