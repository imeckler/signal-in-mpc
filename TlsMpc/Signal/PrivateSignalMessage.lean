import TlsMpc.Signal.PrivateProtobuf

namespace TlsMpc.Signal.PrivateSignalMessage

def message (o : Aes.Ops B) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (withAddresses hasPq : Bool) (version : B)
    (counter previous ratchet cipherKey iv macKey sender receiver plaintext addresses : List B)
    (pq : PrivateBuffer.Buffer B) : PrivateBuffer.Buffer B :=
  let ciphertext := Cbc.encryptCore o cipherKey iv plaintext
  let capacity := ciphertext.length+ratchet.length+addresses.length+pq.data.length+64
  let shape : Serialization.Shape := ⟨5,5,withAddresses⟩
  let content := PrivateSend.join a capacity [
    PrivateSend.literal a capacity [Serialization.versionByte a version],
    PrivateSend.literal a capacity (Serialization.bytesField a 10 (a.const 5::ratchet)),
    PrivateSend.scalar s a capacity 16 counter,PrivateSend.scalar s a capacity 24 previous,
    PrivateSend.literal a capacity (Serialization.bytesField a 34 ciphertext),
    (if hasPq then PrivateProtobuf.bytesField s a 42 pq else PrivateSend.literal a capacity []),
    PrivateSend.literal a capacity (Serialization.addressField a shape addresses)]
  let domain := PrivateSend.join a (capacity+66) [
    PrivateSend.literal a (capacity+66) (MessageMac.identity s sender ++ MessageMac.identity s receiver),content]
  let mac := PrivateHash.hmac s a macKey (capacity+66) domain
  PrivateSend.acceptAddresses a withAddresses addresses
    (PrivateBuffer.append a capacity content (PrivateSend.firstEight a mac))

section Refinement
variable {o : Aes.Ops B} {o' : Aes.Ops B'} {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'}
  {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} {fw : W → W'}
  (ho : Aes.Hom o o' f) (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)
include ho hs ha

theorem message_map (withAddresses hasPq : Bool) (version : B)
    (counter previous ratchet cipherKey iv macKey sender receiver plaintext addresses : List B)
    (pq : PrivateBuffer.Buffer B) :
    (message o s a withAddresses hasPq version counter previous ratchet cipherKey iv macKey sender receiver plaintext addresses pq).map f =
    message o' s' a' withAddresses hasPq (f version) (counter.map f) (previous.map f) (ratchet.map f)
      (cipherKey.map f) (iv.map f) (macKey.map f) (sender.map f) (receiver.map f) (plaintext.map f)
      (addresses.map f) (pq.map f) := by
  have clen := congrArg List.length (Cbc.encryptCore_map ho cipherKey iv plaintext)
  simp only [List.length_map] at clen
  cases hasPq <;>
    simp only [message,Bool.false_eq_true,if_false,if_true,
      PrivateSend.acceptAddresses_map ha,PrivateBuffer.append_map ha,PrivateSend.firstEight_map ha,
      PrivateHash.hmac_map hs ha,PrivateSend.join_map ha,List.map_cons,List.map_nil,PrivateSend.literal_map ha,
      PrivateSend.scalar_map hs ha,PrivateProtobuf.bytesField_map hs ha,
      Serialization.versionByte_map ha,Serialization.bytesField_map ha,Serialization.addressField_map ha,
      Cbc.encryptCore_map ho,MessageMac.identity,hs.byteConst,List.map_append,ha.const,clen,List.length_map]
  all_goals simp only [PrivateBuffer.Buffer.map,List.length_map]

end Refinement
end TlsMpc.Signal.PrivateSignalMessage
