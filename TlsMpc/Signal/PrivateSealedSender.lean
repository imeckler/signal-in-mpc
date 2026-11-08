import TlsMpc.Signal.PrivateProtobuf
import TlsMpc.Signal.SealedSenderV1

/-! SSv1 with a private-length inner SignalMessage. CTR, both KDFs and the
private-length HMAC each execute once; no counter-width profiles are exposed. -/
namespace TlsMpc.Signal.PrivateSealedSender

def encrypt (o : Aes.Ops B) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (cipher mac : List B) (plain : PrivateBuffer.Buffer B) : PrivateBuffer.Buffer B :=
  let input := PrivateBuffer.resize a plain.data.length plain
  let ciphertext := PrivateProtobuf.replaceData a input (SealedSenderV1.ctr o cipher input.data)
  let tag := PrivateProtobuf.first a 10 (PrivateHash.hmac s a mac input.data.length ciphertext)
  PrivateBuffer.append a (input.data.length+10) ciphertext tag

def boundSeal (o : Aes.Ops B) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate expectedSender : List B)
    (inner : PrivateBuffer.Buffer B) : PrivateBuffer.Buffer B :=
  let ephemeral := a.const 5 :: ephemeralPublic
  let recipient := a.const 5 :: recipientPublic
  let sender := a.const 5 :: senderPublic
  let first := SealedSenderV1.material s
    ((TlsKdf.ascii "UnidentifiedDelivery").map s.byteConst ++ recipient ++ ephemeral) ephemeralDh
  let encryptedStatic := SealedSenderV1.encrypt o s ((first.drop 32).take 32) ((first.drop 64).take 32) sender
  let second := SealedSenderV1.material s (first.take 32 ++ encryptedStatic) staticDh
  let innerField := PrivateProtobuf.bytesField s a 26 inner
  let certField := Serialization.bytesField a 18 certificate
  let usmcCap := 2+certField.length+innerField.data.length
  let usmc := PrivateSend.join a usmcCap [
    PrivateSend.literal a usmcCap [a.const 8,a.const 2],
    PrivateSend.literal a usmcCap certField,innerField]
  let encryptedMessage := encrypt o s a ((second.drop 32).take 32) ((second.drop 64).take 32) usmc
  let messageField := PrivateProtobuf.bytesField s a 26 encryptedMessage
  let header := a.const 17 :: (Serialization.bytesField a 10 ephemeral ++ Serialization.bytesField a 18 encryptedStatic)
  let result := PrivateSend.join a (header.length+messageField.data.length)
    [PrivateSend.literal a (header.length+messageField.data.length) header,messageField]
  let status := a.and (SealedSenderV1.agreementMask a ephemeralDh staticDh) (ByteAuth.equalMask a senderPublic expectedSender)
  PrivateProtobuf.gate a status result

theorem encrypt_data_length (o : Aes.Ops B) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (cipher mac : List B) (plain : PrivateBuffer.Buffer B) :
    (encrypt o s a cipher mac plain).data.length = plain.data.length+10 := by
  simp only [encrypt,PrivateProtobuf.append_data_length]
  simp only [PrivateBuffer.resize,PrivateBuffer.finish,PrivateBuffer.make,PrivateBuffer.zero,ByteAuth.release]
  split <;> simp

section Refinement
variable {o : Aes.Ops B} {o' : Aes.Ops B'} {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'}
  {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} {fw : W → W'}
  (ho : Aes.Hom o o' f) (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)
include ho hs ha

theorem encrypt_map (cipher mac : List B) (plain : PrivateBuffer.Buffer B) :
    (encrypt o s a cipher mac plain).map f = encrypt o' s' a' (cipher.map f) (mac.map f) (plain.map f) := by
  have input := PrivateBuffer.resize_map ha plain.data.length plain
  have data := congrArg PrivateBuffer.Buffer.data input
  change List.map f _ = _ at data
  have size := congrArg List.length data
  simp only [List.length_map] at size
  simp only [encrypt,PrivateBuffer.append_map ha,PrivateProtobuf.first_map ha,PrivateHash.hmac_map hs ha,
    PrivateProtobuf.replaceData_map ha,SealedSenderV1.ctr_map ho]
  rw [input,data,size]
  simp only [PrivateBuffer.Buffer.map,List.length_map]

theorem boundSeal_map
    (recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate expectedSender : List B)
    (inner : PrivateBuffer.Buffer B) :
    (boundSeal o s a recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate expectedSender inner).map f =
    boundSeal o' s' a' (recipientPublic.map f) (ephemeralPublic.map f) (senderPublic.map f)
      (ephemeralDh.map f) (staticDh.map f) (certificate.map f) (expectedSender.map f) (inner.map f) := by
  have plen (n : Nat) : (Varint.publicNat a n).length = (Varint.publicNat a' n).length := by
    simpa only [List.length_map] using congrArg List.length (Varint.publicNat_map ha n)
  let first := SealedSenderV1.material s
    ((TlsKdf.ascii "UnidentifiedDelivery").map s.byteConst ++ (a.const 5::recipientPublic) ++ (a.const 5::ephemeralPublic)) ephemeralDh
  have statlen := congrArg List.length (SealedSenderV1.encrypt_map ho hs
    ((first.drop 32).take 32) ((first.drop 64).take 32) (a.const 5::senderPublic))
  dsimp [first] at statlen
  simp only [List.length_map,List.map_take,List.map_drop,SealedSenderV1.material_map hs,List.map_append,
    List.map_cons,List.map_nil,ha.const,List.map_map,Function.comp_def,hs.byteConst] at statlen
  have field := PrivateProtobuf.bytesField_map hs ha 26 inner
  have fdata := congrArg PrivateBuffer.Buffer.data field
  have fsize := congrArg List.length fdata
  simp only [PrivateBuffer.Buffer.map,List.length_map] at fsize
  simp only [boundSeal,PrivateProtobuf.gate_map ha,PrivateSend.join_map ha,List.map_cons,List.map_nil,
    PrivateSend.literal_map ha,PrivateProtobuf.bytesField_map hs ha,encrypt_map ho hs ha,
    SealedSenderV1.material_map hs,SealedSenderV1.encrypt_map ho hs,List.map_append,List.map_take,List.map_drop,
    List.map_map,Function.comp_def,hs.byteConst,Serialization.bytesField_map ha,ha.const,
    ha.and,SealedSenderV1.agreementMask_map ha,ByteAuth.equalMask_map ha]
  simp only [PrivateProtobuf.bytesField_data_length,PrivateProtobuf.join_data_length,encrypt_data_length,
    List.length_cons,List.length_append,List.length_map,PrivateBuffer.Buffer.map,Serialization.bytesField]
  simp only [List.length_cons,List.length_append,List.length_map,plen,statlen]

end Refinement
open Std.Tactic.BVDecide

theorem compiled_boundSeal_correct
    (recipient ephemeral sender edh sdh certificate expected : List (BVExpr 8))
    (inner : PrivateBuffer.Buffer (BVExpr 8)) (assign : BVExpr.Assignment) :
    PrivateProtobuf.CircuitAgreement
      (PrivateBuffer.output ByteAuth.symbolic (boundSeal Aes.symbolic Sha256.symbolic ByteAuth.symbolic
        recipient ephemeral sender edh sdh certificate expected inner))
      (PrivateBuffer.output ByteAuth.concrete (boundSeal Aes.concrete Sha256.concrete ByteAuth.concrete
        (recipient.map (BVExpr.eval assign)) (ephemeral.map (BVExpr.eval assign)) (sender.map (BVExpr.eval assign))
        (edh.map (BVExpr.eval assign)) (sdh.map (BVExpr.eval assign)) (certificate.map (BVExpr.eval assign))
        (expected.map (BVExpr.eval assign)) (inner.map (BVExpr.eval assign)))) assign := by
  intro index hi
  rw [ByteCircuit.compile_bytes_correct,PrivateBuffer.output_map (ByteAuth.evaluationHom assign),
    boundSeal_map (Aes.evaluationHom assign) (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]

end TlsMpc.Signal.PrivateSealedSender
