import TlsMpc.Signal.PrivateSignalMessage

/-! Canonical private-length PreKeySignalMessage, one-time-prekey/Kyber1024
profile. The caller supplies actual computed initial Signal/KEM outputs; upstream
validity remains mandatory. All IDs use canonical private uint32 widths, not
host-supplied width metadata. No store mutation or bootstrap authorization. -/
namespace TlsMpc.Signal.PrivatePreKeyMessageV1
open Std.Tactic.BVDecide

def message (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (upstream : B)
 (registration oneTime signedId kemId base identity ciphertext : List B)
 (signal : PrivateBuffer.Buffer B) : PrivateBuffer.Buffer B :=
 let cap := signal.data.length+1700
 let shape := if registration.length=4 ∧ oneTime.length=4 ∧ signedId.length=4 ∧ kemId.length=4 ∧
  base.length=32 ∧ identity.length=32 ∧ ciphertext.length=1569 then a.const 255 else a.const 0
 let ok := a.and shape (a.and (ByteAuth.eqMask a upstream (a.const 255))
  (ByteAuth.eqMask a (OpenResult.get a ciphertext 0) (a.const 8)))
 let wire := PrivateSend.join a cap [
  PrivateSend.literal a cap [a.const 68],
  PrivateSend.scalar s a cap 8 oneTime,
  PrivateSend.literal a cap (Serialization.bytesField a 18 (a.const 5::base)),
  PrivateSend.literal a cap (Serialization.bytesField a 26 (a.const 5::identity)),
  PrivateProtobuf.bytesField s a 34 signal,
  PrivateSend.scalar s a cap 40 registration,
  PrivateSend.scalar s a cap 48 signedId,
  PrivateSend.scalar s a cap 56 kemId,
  PrivateSend.literal a cap (Serialization.bytesField a 66 ciphertext)]
 PrivateProtobuf.gate a ok wire

section
variable {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'}
 {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} {fw : W → W'}
 (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)
include hs ha

theorem message_map (upstream : B) (registration oneTime signedId kemId base identity ciphertext : List B)
 (signal : PrivateBuffer.Buffer B) :
 (message s a upstream registration oneTime signedId kemId base identity ciphertext signal).map f =
 message s' a' (f upstream) (registration.map f) (oneTime.map f) (signedId.map f) (kemId.map f)
  (base.map f) (identity.map f) (ciphertext.map f) (signal.map f) := by
 simp only [message,List.length_map]
 split <;> simp only [PrivateProtobuf.gate_map ha,PrivateSend.join_map ha,
  PrivateSend.literal_map ha,PrivateSend.scalar_map hs ha,PrivateProtobuf.bytesField_map hs ha,
  List.map_cons,List.map_nil,ha.const,ha.and,ByteAuth.eqMask_map ha,OpenResult.get_map ha,
  Serialization.bytesField_map ha]
 all_goals simp only [PrivateBuffer.Buffer.map,List.length_map]
end

theorem compiled_message_correct (upstream : BVExpr 8)
 (registration oneTime signedId kemId base identity ciphertext : List (BVExpr 8))
 (signal : PrivateBuffer.Buffer (BVExpr 8)) (assign : BVExpr.Assignment) :
 PrivateProtobuf.CircuitAgreement
  (PrivateBuffer.output ByteAuth.symbolic
   (message Sha256.symbolic ByteAuth.symbolic upstream registration oneTime signedId kemId base identity ciphertext signal))
  (PrivateBuffer.output ByteAuth.concrete
   (message Sha256.concrete ByteAuth.concrete (BVExpr.eval assign upstream)
    (registration.map (BVExpr.eval assign)) (oneTime.map (BVExpr.eval assign))
    (signedId.map (BVExpr.eval assign)) (kemId.map (BVExpr.eval assign))
    (base.map (BVExpr.eval assign)) (identity.map (BVExpr.eval assign)) (ciphertext.map (BVExpr.eval assign))
    (signal.map (BVExpr.eval assign)))) assign := by
 intro index hi
 rw [ByteCircuit.compile_bytes_correct,PrivateBuffer.output_map (ByteAuth.evaluationHom assign),
  message_map (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]
end TlsMpc.Signal.PrivatePreKeyMessageV1
