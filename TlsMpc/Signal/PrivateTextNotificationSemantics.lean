import TlsMpc.Signal.PrivateTextNotification
import TlsMpc.Signal.PrivateBufferRecordSemantics

/-! Exact semantics of the actual bounded ISO7816 padding expression used by
PrivateTextNotification.build, relative to the preceding Content buffer's
canonical record. This does not assume correctness of protobuf/UTF8 encoding.
It isolates the remaining upstream obligation rather than replacing it with a
supplied acceptance flag. Payload lengths below are proof witnesses, not inputs. -/
namespace TlsMpc.Signal.PrivateTextNotification
open PrivateBuffer

theorem iso7816_contents (sourceCapacity : Nat) (content : List (BitVec 8))
    (fit : content.length<80) :
    PrivateSend.join ByteAuth.concrete 80 [ofContents sourceCapacity content,
      PrivateSend.literal ByteAuth.concrete 80 [128]] = ofContents 80 (content++[128]) := by
  unfold PrivateSend.join PrivateSend.literal
  simp only [List.foldl_cons,List.foldl_nil]
  rw [fromPublic_contents 80 (by decide) [] (by simp),
    fromPublic_contents 80 (by decide) [128] (by simp)]
  rw [append_contents 80 80 sourceCapacity (by decide) [] content (by simp;omega)]
  simp only [List.nil_append]
  exact append_contents 80 80 80 (by decide) content [128] (by simp;omega)

theorem iso7816_data (sourceCapacity : Nat) (content : List (BitVec 8))
    (fit : content.length<80) :
    (PrivateSend.join ByteAuth.concrete 80 [ofContents sourceCapacity content,
      PrivateSend.literal ByteAuth.concrete 80 [128]]).data =
      content ++ 128 :: List.replicate (79-content.length) 0 := by
  rw [iso7816_contents sourceCapacity content fit]
  have count : 80-(content++[128]).length=79-content.length := by simp
  simp only [ofContents,count,List.append_assoc,List.singleton_append]

theorem iso7816_status (sourceCapacity : Nat) (content : List (BitVec 8))
    (fit : content.length<80) :
    (PrivateSend.join ByteAuth.concrete 80 [ofContents sourceCapacity content,
      PrivateSend.literal ByteAuth.concrete 80 [128]]).valid=255 := by
  rw [iso7816_contents sourceCapacity content fit];rfl

theorem iso7816_payload_prefix (sourceCapacity : Nat) (content : List (BitVec 8))
    (fit : content.length<80) :
    (PrivateSend.join ByteAuth.concrete 80 [ofContents sourceCapacity content,
      PrivateSend.literal ByteAuth.concrete 80 [128]]).data.take content.length=content := by
  rw [iso7816_data sourceCapacity content fit]
  simp

theorem iso7816_terminator_and_zeros (sourceCapacity : Nat) (content : List (BitVec 8))
    (fit : content.length<80) :
    (PrivateSend.join ByteAuth.concrete 80 [ofContents sourceCapacity content,
      PrivateSend.literal ByteAuth.concrete 80 [128]]).data.drop content.length =
      128 :: List.replicate (79-content.length) 0 := by
  rw [iso7816_data sourceCapacity content fit]
  simp
end TlsMpc.Signal.PrivateTextNotification
