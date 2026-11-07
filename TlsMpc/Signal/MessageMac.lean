import TlsMpc.HmacPrepared
import TlsMpc.ByteAuth

/-! SignalMessage MAC domain from pinned libsignal protocol.rs::compute_mac:
serialized sender identity key || serialized receiver identity key || content,
with the first eight HMAC-SHA256 bytes retained. Each identity input is the
32-byte Curve25519 public-key encoding; serialization prepends key type 0x05.
The complete RustCrypto HMAC wrapper refinement is still pending. -/

namespace TlsMpc.Signal.MessageMac
open Std.Tactic.BVDecide

def identity (o : Sha256.Ops B W) (raw : List B) : List B := o.byteConst 5 :: raw

def tag (o : Sha256.Ops B W) (macKey sender receiver content : List B) : List B :=
  (HmacPrepared.run o (HmacPrepared.prepare o macKey)
    (identity o sender ++ identity o receiver ++ content)).take 8

def content (wire : List B) : List B := wire.take (wire.length - 8)
def receivedTag (wire : List B) : List B := wire.drop (wire.length - 8)

def verifyMask (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (macKey sender receiver wire : List B) : B :=
  ByteAuth.equalMask a (tag s macKey sender receiver (content wire)) (receivedTag wire)

def tagChecked (o : Sha256.Ops B W) (macKey sender receiver bytes : List B) : Option (List B) :=
  if macKey.length = 32 ∧ sender.length = 32 ∧ receiver.length = 32 ∧
      bytes.length + 130 < 2 ^ 61 then some (tag o macKey sender receiver bytes) else none

theorem tag_length (o : Sha256.Ops B W) (macKey sender receiver bytes : List B) :
    (tag o macKey sender receiver bytes).length = 8 := by
  simp [tag, HmacPrepared.run_prepare, Sha256.hmac_length]

section Refinement
variable {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'}
  {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} {fw : W → W'}
  (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)
include hs

theorem tag_map (macKey sender receiver bytes : List B) :
    (tag s macKey sender receiver bytes).map f =
      tag s' (macKey.map f) (sender.map f) (receiver.map f) (bytes.map f) := by
  simp only [tag, HmacPrepared.run_prepare, List.map_take, Sha256.hmac_map hs,
    List.map_append, identity, List.map_cons, hs.byteConst]

include ha in
theorem verifyMask_map (macKey sender receiver wire : List B) :
    f (verifyMask s a macKey sender receiver wire) =
      verifyMask s' a' (macKey.map f) (sender.map f) (receiver.map f) (wire.map f) := by
  simp only [verifyMask, ByteAuth.equalMask_map ha, tag_map hs,
    content, receivedTag, List.map_take, List.map_drop, List.length_map]

theorem tagChecked_map (macKey sender receiver bytes : List B) :
    (tagChecked s macKey sender receiver bytes).map (List.map f) =
      tagChecked s' (macKey.map f) (sender.map f) (receiver.map f) (bytes.map f) := by
  simp only [tagChecked, List.length_map]
  split <;> simp_all [tag_map hs]

end Refinement

theorem verifyMask_value (macKey sender receiver wire : List (BitVec 8)) :
    verifyMask Sha256.concrete ByteAuth.concrete macKey sender receiver wire =
      if tag Sha256.concrete macKey sender receiver (content wire) = receivedTag wire then 255 else 0 :=
  ByteAuth.equalMask_value _ _

theorem compiled_tag_correct (macKey sender receiver bytes : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (tag Sha256.symbolic macKey sender receiver bytes).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile
        (ByteCircuit.joinExpr (tag Sha256.symbolic macKey sender receiver bytes))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile
        (ByteCircuit.joinExpr (tag Sha256.symbolic macKey sender receiver bytes))).vec.get index hi)) =
      (ByteCircuit.joinValue (tag Sha256.concrete (macKey.map (BVExpr.eval assign))
        (sender.map (BVExpr.eval assign)) (receiver.map (BVExpr.eval assign))
        (bytes.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, tag_map (Sha256.evaluationHom assign)]

end TlsMpc.Signal.MessageMac
