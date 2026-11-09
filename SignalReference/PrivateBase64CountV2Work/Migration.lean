import TlsMpc.Signal.PrivateRelay
namespace TlsMpc.Signal.PrivateBase64CountV2.Migration
open RelayEncoding
def legacyBody (d : DecimalOps B W) (v : Varint64.Ops B W) (a : ByteAuth.Ops B)
    (metadata : List B) (sealed : PrivateBuffer.Buffer B) : PrivateBuffer.Buffer B :=
  let content := PrivateBase64.encode a sealed
  let cap := content.data.length+256
  PrivateSend.join a cap [
    PrivateSend.literal a cap (literal a "{\"messages\":[{\"content\":\""),content,
    PrivateSend.literal a cap (literal a "\",\"destinationDeviceId\":"),
    PrivateDecimal.encode d a (RelayRequest.word v a metadata 48 1),
    PrivateSend.literal a cap (literal a ",\"destinationRegistrationId\":"),
    PrivateDecimal.encode d a (RelayRequest.word v a metadata 49 4),
    PrivateSend.literal a cap (literal a ",\"type\":6}],\"online\":false,\"timestamp\":"),
    PrivateDecimal.encode d a (RelayRequest.word v a metadata 32 8),
    PrivateSend.literal a cap (literal a ",\"urgent\":true}")]

theorem body_eq_reference (d : DecimalOps (BitVec 8) W) (v : Varint64.Ops (BitVec 8) W)
    (metadata : List (BitVec 8)) (sealed : PrivateBuffer.Buffer (BitVec 8)) :
    PrivateRelay.body d v ByteAuth.concrete metadata sealed=legacyBody d v ByteAuth.concrete metadata sealed := by
  simp only [PrivateRelay.body,legacyBody,PrivateBase64CountV2.encode_correct]
end TlsMpc.Signal.PrivateBase64CountV2.Migration
#print axioms TlsMpc.Signal.PrivateBase64CountV2.Migration.body_eq_reference
