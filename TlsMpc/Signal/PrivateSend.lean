import TlsMpc.Signal.PrivateVarint
import TlsMpc.Signal.PrivateHash
import TlsMpc.Signal.Send

/-! Established SignalMessage construction without public counter-width
profiles. Ciphertext and HMAC are each computed once; private canonical
counter lengths flow through bounded serialization and HMAC padding. -/
namespace TlsMpc.Signal.PrivateSend
open Std.Tactic.BVDecide

def join (a : ByteAuth.Ops B) (capacity : Nat) (chunks : List (PrivateBuffer.Buffer B)) : PrivateBuffer.Buffer B :=
  chunks.foldl (PrivateBuffer.append a capacity) (PrivateBuffer.fromPublic a capacity [])

def literal (a : ByteAuth.Ops B) (capacity : Nat) (raw : List B) : PrivateBuffer.Buffer B :=
  PrivateBuffer.fromPublic a capacity raw

def scalar (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (capacity tag : Nat) (raw : List B) : PrivateBuffer.Buffer B :=
  join a capacity [literal a capacity [a.const tag],PrivateVarint.uint32 s a (Varint.pack s a raw)]

def firstEight (a : ByteAuth.Ops B) (mac : PrivateBuffer.Buffer B) : PrivateBuffer.Buffer B :=
  PrivateBuffer.finish a mac.valid (PrivateBuffer.publicLength a 8) (mac.data.take 8)

def acceptAddresses (a : ByteAuth.Ops B) (withAddresses : Bool) (addresses : List B)
    (result : PrivateBuffer.Buffer B) : PrivateBuffer.Buffer B :=
  PrivateBuffer.finish a (a.and result.valid
    (if withAddresses then Receive.expectedAddressMask a addresses else a.const 255)) result.lengthBits result.data

def message (o : Aes.Ops B) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (withAddresses : Bool) (version : B)
    (counter previous ratchet cipherKey iv macKey sender receiver plaintext pq addresses : List B) : PrivateBuffer.Buffer B :=
  let ciphertext := Cbc.encryptCore o cipherKey iv plaintext
  let shape : Serialization.Shape := ⟨5,5,withAddresses⟩
  let capacity := (Serialization.content s a shape version counter previous ratchet ciphertext pq addresses).length+8
  let content := join a capacity [
    literal a capacity [Serialization.versionByte a version],
    literal a capacity (Serialization.bytesField a 10 (a.const 5::ratchet)),
    scalar s a capacity 16 counter,scalar s a capacity 24 previous,
    literal a capacity (Serialization.bytesField a 34 ciphertext),
    literal a capacity (Serialization.pqField a pq),
    literal a capacity (Serialization.addressField a shape addresses)]
  let domain := join a (capacity+66) [
    literal a (capacity+66) (MessageMac.identity s sender ++ MessageMac.identity s receiver),content]
  let mac := PrivateHash.hmac s a macKey (capacity+66) domain
  acceptAddresses a withAddresses addresses (PrivateBuffer.append a capacity content (firstEight a mac))

section Refinement
variable {o : Aes.Ops B} {o' : Aes.Ops B'} {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'}
  {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} {fw : W → W'}
  (ho : Aes.Hom o o' f) (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)
include ha

theorem join_map (capacity : Nat) (chunks : List (PrivateBuffer.Buffer B)) :
    (join a capacity chunks).map f = join a' capacity (chunks.map (PrivateBuffer.Buffer.map f)) := by
  have aux (chunks : List (PrivateBuffer.Buffer B)) (initial : PrivateBuffer.Buffer B) :
      (chunks.foldl (PrivateBuffer.append a capacity) initial).map f =
      (chunks.map (PrivateBuffer.Buffer.map f)).foldl (PrivateBuffer.append a' capacity) (initial.map f) := by
    induction chunks generalizing initial with
    | nil => rfl
    | cons x xs ih => simp only [List.foldl_cons,List.map_cons,ih,PrivateBuffer.append_map ha]
  simp only [join,aux,PrivateBuffer.fromPublic_map ha,List.map_nil]

theorem literal_map (capacity : Nat) (raw : List B) :
    (literal a capacity raw).map f = literal a' capacity (raw.map f) := PrivateBuffer.fromPublic_map ha capacity raw
theorem firstEight_map (mac : PrivateBuffer.Buffer B) :
    (firstEight a mac).map f = firstEight a' (mac.map f) := by
  unfold firstEight
  rw [PrivateBuffer.finish_map ha,PrivateBuffer.publicLength_map ha]
  simp only [PrivateBuffer.Buffer.map,List.map_take]

theorem acceptAddresses_map (withAddresses : Bool) (addresses : List B) (result : PrivateBuffer.Buffer B) :
    (acceptAddresses a withAddresses addresses result).map f =
      acceptAddresses a' withAddresses (addresses.map f) (result.map f) := by
  unfold acceptAddresses
  rw [PrivateBuffer.finish_map ha,ha.and]
  simp only [PrivateBuffer.Buffer.map]
  split <;> simp only [Receive.expectedAddressMask_map ha,ha.const]

include hs

theorem scalar_map (capacity tag : Nat) (raw : List B) :
    (scalar s a capacity tag raw).map f = scalar s' a' capacity tag (raw.map f) := by
  simp only [scalar,join_map ha,List.map_cons,List.map_nil,literal_map ha,ha.const,
    PrivateVarint.uint32_map hs ha,Varint.pack_map hs ha]
include ho

theorem message_map (withAddresses : Bool) (version : B)
    (counter previous ratchet cipherKey iv macKey sender receiver plaintext pq addresses : List B) :
    (message o s a withAddresses version counter previous ratchet cipherKey iv macKey sender receiver plaintext pq addresses).map f =
    message o' s' a' withAddresses (f version) (counter.map f) (previous.map f) (ratchet.map f)
      (cipherKey.map f) (iv.map f) (macKey.map f) (sender.map f) (receiver.map f)
      (plaintext.map f) (pq.map f) (addresses.map f) := by
  have content := Serialization.content_map hs ha (Serialization.Shape.mk 5 5 withAddresses)
    version counter previous ratchet (Cbc.encryptCore o cipherKey iv plaintext) pq addresses
  have clen := congrArg List.length content
  simp only [List.length_map,Cbc.encryptCore_map ho] at clen
  simp only [message,clen,acceptAddresses_map ha,PrivateBuffer.append_map ha,firstEight_map ha,
    PrivateHash.hmac_map hs ha,join_map ha,List.map_cons,List.map_nil,literal_map ha,scalar_map hs ha,
    Serialization.versionByte_map ha,Serialization.bytesField_map ha,Serialization.pqField_map ha,
    Serialization.addressField_map ha,List.map_append,List.map_take,Cbc.encryptCore_map ho,ha.const,
    MessageMac.identity,hs.byteConst]

end Refinement
theorem compiled_message_correct (withAddresses : Bool) (version : BVExpr 8)
    (counter previous ratchet cipherKey iv macKey sender receiver plaintext pq addresses : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8*(PrivateBuffer.output ByteAuth.symbolic
      (message Aes.symbolic Sha256.symbolic ByteAuth.symbolic withAddresses version
        counter previous ratchet cipherKey iv macKey sender receiver plaintext pq addresses)).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (PrivateBuffer.output ByteAuth.symbolic (message Aes.symbolic Sha256.symbolic ByteAuth.symbolic
        withAddresses version counter previous ratchet cipherKey iv macKey sender receiver plaintext pq addresses)))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (PrivateBuffer.output ByteAuth.symbolic (message Aes.symbolic Sha256.symbolic ByteAuth.symbolic
          withAddresses version counter previous ratchet cipherKey iv macKey sender receiver plaintext pq addresses)))).vec.get index hi)) =
    (ByteCircuit.joinValue (PrivateBuffer.output ByteAuth.concrete
      (message Aes.concrete Sha256.concrete ByteAuth.concrete withAddresses (version.eval assign)
        (counter.map (BVExpr.eval assign)) (previous.map (BVExpr.eval assign)) (ratchet.map (BVExpr.eval assign))
        (cipherKey.map (BVExpr.eval assign)) (iv.map (BVExpr.eval assign)) (macKey.map (BVExpr.eval assign))
        (sender.map (BVExpr.eval assign)) (receiver.map (BVExpr.eval assign)) (plaintext.map (BVExpr.eval assign))
        (pq.map (BVExpr.eval assign)) (addresses.map (BVExpr.eval assign))))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,PrivateBuffer.output_map (ByteAuth.evaluationHom assign),
    message_map (Aes.evaluationHom assign) (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]

end TlsMpc.Signal.PrivateSend
