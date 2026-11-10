import TlsMpc.Signal.PrivateBootstrapSendV1
import TlsMpc.Signal.PrivateInitialSpqrV1Proofs
namespace TlsMpc.Signal.PrivateBootstrapSendV1
open Std.Tactic.BVDecide
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
section
variable {o : Aes.Ops B} {o' : Aes.Ops B'} {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'}
 {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} {fw : W → W'}
 (ho : Aes.Hom o o' f) (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)

theorem part_map (raw : List B) (offset size : Nat) :
 (part raw offset size).map f = part (raw.map f) offset size := by
 simp only [part,List.map_take,List.map_drop]
include hs ha in
theorem prekey_valid_map (mask : B) (registration otp signedId kemId base identity ct : List B)
 (signal : PrivateBuffer.Buffer B) :
 f (PrivatePreKeyMessageV1.message s a mask registration otp signedId kemId base identity ct signal).valid =
 (PrivatePreKeyMessageV1.message s' a' (f mask) (registration.map f) (otp.map f)
  (signedId.map f) (kemId.map f) (base.map f) (identity.map f) (ct.map f) (signal.map f)).valid := by
 have h := congrArg PrivateBuffer.Buffer.valid
  (PrivatePreKeyMessageV1.message_map hs ha mask registration otp signedId kemId base identity ct signal)
 simpa only [PrivateBuffer.Buffer.map] using h
include hs ha in
theorem senderAfter_map (old chain : List B) :
 (senderAfter s a old chain).map f = senderAfter s' a' (old.map f) (chain.map f) := by
 simp only [senderAfter,List.map_append,List.map_take,ChainSend.nextCounter_map hs ha,part_map]
include ho hs ha in
theorem inner_map (sender own peer addresses plaintext pqWire pqKey : List B) :
 ((inner o s a sender own peer addresses plaintext pqWire pqKey).1.map f,
  (inner o s a sender own peer addresses plaintext pqWire pqKey).2.map f) =
 inner o' s' a' (sender.map f) (own.map f) (peer.map f) (addresses.map f)
  (plaintext.map f) (pqWire.map f) (pqKey.map f) := by
 have hd := ChainSend.deriveFast_map hs (chainKey := part sender 96 32) (pqKey := pqKey)
 simp only [Symmetric.Step.map,Symmetric.Material.map,part_map] at hd
 have hk := congrArg Symmetric.Step.nextChainKey hd
 have hc := congrArg (fun d=>d.material.cipherKey) hd
 have hm := congrArg (fun d=>d.material.macKey) hd
 have hi := congrArg (fun d=>d.material.iv) hd
 simp only at hk hc hm hi
 simp only [inner,PrivateBuffer.resize_map ha,PrivateSignalMessage.message_map ho hs ha,
  part_map,hc,hi,hm,ha.const,PrivateBuffer.fromPublic_map ha,senderAfter_map hs ha,hk]

include ho hs ha in
theorem first_map (keys generated own peer metadata addresses plaintext ciphertext : List B) (textValid : B) :
 (first o s a keys generated own peer metadata addresses plaintext ciphertext textValid).map f =
 first o' s' a' (keys.map f) (generated.map f) (own.map f) (peer.map f)
  (metadata.map f) (addresses.map f) (plaintext.map f) (ciphertext.map f) (f textValid) := by
 have hi := inner_map ho hs ha (part keys 33 136) own peer addresses plaintext
  (part (PrivateInitialSpqrV1.start s a (part keys 514 32) generated) 3842 37)
  (part (PrivateInitialSpqrV1.start s a (part keys 514 32) generated) 3879 32)
 have hwire := congrArg Prod.fst hi
 have hstate := congrArg Prod.snd hi
 simp only [part_map,PrivateInitialSpqrV1.start_map hs ha] at hwire hstate
 simp only [first,List.length_map]
 split <;> simp only [List.map_cons,List.map_append,List.map_take,ha.and,ha.const,
  OpenResult.get_map ha,ByteAuth.eqMask_map ha,ByteAuth.release_map ha,
  PrivateBuffer.output_map ha,prekey_valid_map hs ha,PrivatePreKeyMessageV1.message_map hs ha,part_map,
  PrivateInitialSpqrV1.start_map hs ha,hwire,hstate]


include ho hs ha in
theorem second_map (old plaintext : List B) (textValid : B) :
 (second o s a old plaintext textValid).map f =
 second o' s' a' (old.map f) (plaintext.map f) (f textValid) := by
 have hi := inner_map ho hs ha (part (old.drop 1) 1717 136) ((old.drop 1).take 32)
  (part (old.drop 1) 32 32) (part (old.drop 1) 1681 36) plaintext
  (part (PrivateInitialSpqrV1.second s a (OpenResult.get a old 0 :: part (old.drop 1) 2198 3841)) 3842 37)
  (part (PrivateInitialSpqrV1.second s a (OpenResult.get a old 0 :: part (old.drop 1) 2198 3841)) 3879 32)
 have hwire := congrArg Prod.fst hi
 have hstate := congrArg Prod.snd hi
 simp only [part_map,List.map_take,List.map_drop,List.map_cons,OpenResult.get_map ha,
  PrivateInitialSpqrV1.second_map hs ha] at hwire hstate
 simp only [second,List.length_map]
 split <;> simp only [List.map_cons,List.map_append,List.map_take,List.map_drop,ha.and,ha.const,
  OpenResult.get_map ha,ByteAuth.eqMask_map ha,ChainSend.selectState_map ha,
  PrivateBuffer.output_map ha,prekey_valid_map hs ha,PrivatePreKeyMessageV1.message_map hs ha,part_map,
  PrivateInitialSpqrV1.second_map hs ha,hwire,hstate]

end

theorem compiled_first_correct (keys generated own peer metadata addresses plaintext ciphertext : List (BVExpr 8))
 (valid : BVExpr 8) (assign : BVExpr.Assignment) :
 PrivateProtobuf.CircuitAgreement
  (first Aes.symbolic Sha256.symbolic ByteAuth.symbolic keys generated own peer metadata addresses plaintext ciphertext valid)
  (first Aes.concrete Sha256.concrete ByteAuth.concrete (keys.map (BVExpr.eval assign))
   (generated.map (BVExpr.eval assign)) (own.map (BVExpr.eval assign)) (peer.map (BVExpr.eval assign))
   (metadata.map (BVExpr.eval assign)) (addresses.map (BVExpr.eval assign))
   (plaintext.map (BVExpr.eval assign)) (ciphertext.map (BVExpr.eval assign)) (BVExpr.eval assign valid)) assign := by
 intro index hi
 rw [ByteCircuit.compile_bytes_correct,first_map (Aes.evaluationHom assign) (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]

theorem compiled_second_correct (old plaintext : List (BVExpr 8)) (valid : BVExpr 8)
 (assign : BVExpr.Assignment) :
 PrivateProtobuf.CircuitAgreement
  (second Aes.symbolic Sha256.symbolic ByteAuth.symbolic old plaintext valid)
  (second Aes.concrete Sha256.concrete ByteAuth.concrete (old.map (BVExpr.eval assign))
   (plaintext.map (BVExpr.eval assign)) (BVExpr.eval assign valid)) assign := by
 intro index hi
 rw [ByteCircuit.compile_bytes_correct,second_map (Aes.evaluationHom assign) (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]
end TlsMpc.Signal.PrivateBootstrapSendV1
