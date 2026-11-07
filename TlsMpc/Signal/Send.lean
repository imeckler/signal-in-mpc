import TlsMpc.Signal.Serialization
import TlsMpc.Signal.Cbc

/-! Established-message send composition. AES-256-CBC ciphertext is produced
inside the circuit, serialized once, and the MAC covers those same content
bytes. The result is secret status || complete SignalMessage wire bytes.
This operation consumes already derived message keys and typed identity/
ratchet/address inputs; it does not update or persist a ratchet session. -/

namespace TlsMpc.Signal.Send
open Std.Tactic.BVDecide

def message (o : Aes.Ops B) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (shape : Serialization.Shape) (version : B)
    (counter previous ratchet cipherKey iv macKey sender receiver plaintext pq addresses : List B) : List B :=
  let ciphertext := Cbc.encryptCore o cipherKey iv plaintext
  let content := Serialization.content s a shape version counter previous ratchet ciphertext pq addresses
  content ++ MessageMac.tag s macKey sender receiver content

def sealCore (o : Aes.Ops B) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (shape : Serialization.Shape) (version : B)
    (counter previous ratchet cipherKey iv macKey sender receiver plaintext pq addresses : List B) : List B :=
  let accepted := Serialization.acceptedMask s a shape counter previous addresses
  accepted :: ByteAuth.release a accepted
    (message o s a shape version counter previous ratchet cipherKey iv macKey sender receiver plaintext pq addresses)

def sealChecked (o : Aes.Ops B) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (shape : Serialization.Shape) (version : B)
    (counter previous ratchet cipherKey iv macKey sender receiver plaintext pq addresses : List B) : Option (List B) :=
  if Serialization.inputShape shape counter previous ratchet plaintext pq addresses ∧
      cipherKey.length = 32 ∧ iv.length = 16 ∧ macKey.length = 32 ∧
      sender.length = 32 ∧ receiver.length = 32 ∧
      plaintext.length + pq.length + 256 < 2 ^ 61 then
    some (sealCore o s a shape version counter previous ratchet cipherKey iv macKey sender receiver plaintext pq addresses)
  else none

section Refinement
variable {o : Aes.Ops B} {o' : Aes.Ops B'} {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'}
  {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} {fw : W → W'}
  (ho : Aes.Hom o o' f) (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)
include ho hs ha

theorem message_map (shape : Serialization.Shape) (version : B)
    (counter previous ratchet cipherKey iv macKey sender receiver plaintext pq addresses : List B) :
    (message o s a shape version counter previous ratchet cipherKey iv macKey sender receiver plaintext pq addresses).map f =
      message o' s' a' shape (f version) (counter.map f) (previous.map f) (ratchet.map f)
        (cipherKey.map f) (iv.map f) (macKey.map f) (sender.map f) (receiver.map f)
        (plaintext.map f) (pq.map f) (addresses.map f) := by
  simp only [message, List.map_append, Serialization.content_map hs ha,
    Cbc.encryptCore_map ho, MessageMac.tag_map hs]

theorem sealCore_map (shape : Serialization.Shape) (version : B)
    (counter previous ratchet cipherKey iv macKey sender receiver plaintext pq addresses : List B) :
    (sealCore o s a shape version counter previous ratchet cipherKey iv macKey sender receiver plaintext pq addresses).map f =
      sealCore o' s' a' shape (f version) (counter.map f) (previous.map f) (ratchet.map f)
        (cipherKey.map f) (iv.map f) (macKey.map f) (sender.map f) (receiver.map f)
        (plaintext.map f) (pq.map f) (addresses.map f) := by
  simp only [sealCore, List.map_cons, ByteAuth.release_map ha,
    Serialization.acceptedMask_map hs ha, message_map ho hs ha]

theorem sealChecked_map (shape : Serialization.Shape) (version : B)
    (counter previous ratchet cipherKey iv macKey sender receiver plaintext pq addresses : List B) :
    (sealChecked o s a shape version counter previous ratchet cipherKey iv macKey sender receiver plaintext pq addresses).map (List.map f) =
      sealChecked o' s' a' shape (f version) (counter.map f) (previous.map f) (ratchet.map f)
        (cipherKey.map f) (iv.map f) (macKey.map f) (sender.map f) (receiver.map f)
        (plaintext.map f) (pq.map f) (addresses.map f) := by
  simp only [sealChecked, Serialization.inputShape, List.length_map]
  split <;> simp [sealCore_map ho hs ha]

end Refinement

theorem sealCore_concrete_correct (shape : Serialization.Shape) (version : BitVec 8)
    (counter previous ratchet cipherKey iv macKey sender receiver plaintext pq addresses : List (BitVec 8)) :
    sealCore Aes.concrete Sha256.concrete ByteAuth.concrete shape version
      counter previous ratchet cipherKey iv macKey sender receiver plaintext pq addresses =
      if Serialization.accepted shape counter previous addresses then
        255 :: message Aes.concrete Sha256.concrete ByteAuth.concrete shape version
          counter previous ratchet cipherKey iv macKey sender receiver plaintext pq addresses
      else List.replicate (1 + (message Aes.concrete Sha256.concrete ByteAuth.concrete shape version
        counter previous ratchet cipherKey iv macKey sender receiver plaintext pq addresses).length) 0 := by
  simp only [sealCore, Serialization.acceptedMask_value]
  split
  · rw [ByteAuth.release_accept]
  · rw [ByteAuth.release_reject, Nat.add_comm 1, List.replicate_succ]

theorem compiled_sealCore_correct (shape : Serialization.Shape) (version : BVExpr 8)
    (counter previous ratchet cipherKey iv macKey sender receiver plaintext pq addresses : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (sealCore Aes.symbolic Sha256.symbolic ByteAuth.symbolic shape version
      counter previous ratchet cipherKey iv macKey sender receiver plaintext pq addresses).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (sealCore Aes.symbolic Sha256.symbolic ByteAuth.symbolic shape version
          counter previous ratchet cipherKey iv macKey sender receiver plaintext pq addresses))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (sealCore Aes.symbolic Sha256.symbolic ByteAuth.symbolic shape version
          counter previous ratchet cipherKey iv macKey sender receiver plaintext pq addresses))).vec.get index hi)) =
      (ByteCircuit.joinValue (sealCore Aes.concrete Sha256.concrete ByteAuth.concrete shape (version.eval assign)
        (counter.map (BVExpr.eval assign)) (previous.map (BVExpr.eval assign)) (ratchet.map (BVExpr.eval assign))
        (cipherKey.map (BVExpr.eval assign)) (iv.map (BVExpr.eval assign)) (macKey.map (BVExpr.eval assign))
        (sender.map (BVExpr.eval assign)) (receiver.map (BVExpr.eval assign)) (plaintext.map (BVExpr.eval assign))
        (pq.map (BVExpr.eval assign)) (addresses.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, sealCore_map (Aes.evaluationHom assign)
    (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]

end TlsMpc.Signal.Send
