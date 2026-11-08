import TlsMpc.Signal.Serialization
import TlsMpc.Signal.Symmetric
import TlsMpc.Aes

/-! Sealed Sender v1 symmetric envelope for an established-session MESSAGE.
Matches the selected pinned libsignal KDF/CTR/HMAC/protobuf operations. Both DH
results must be produced by a private curve-agreement implementation; this
module neither supplies assumed validity flags nor proves that boundary.
Sender certificate validation and fresh ephemeral generation remain separate. -/
namespace TlsMpc.Signal.SealedSenderV1
open Std.Tactic.BVDecide

def counter (o : Aes.Ops B) (n : Nat) : List B :=
  List.replicate 12 (o.const 0) ++ (List.range 4).map (fun i => o.const (n / 2^(8*(3-i))))

def ctrLoop (o : Aes.Ops B) (expanded : List B) : Nat → Nat → List B → List B
  | 0,_,_ => []
  | n+1,index,plain =>
    let stream := Aes.encryptExpanded o 14 expanded (counter o index)
    (plain.take 16).zipWith o.xor stream ++ ctrLoop o expanded n (index+1) (plain.drop 16)

def ctr (o : Aes.Ops B) (key plain : List B) : List B :=
  ctrLoop o (Aes.expandKey o 8 14 key) ((plain.length+15)/16) 0 plain

def encrypt (o : Aes.Ops B) (s : Sha256.Ops B W) (cipher mac plain : List B) : List B :=
  let ciphertext := ctr o cipher plain
  ciphertext ++ (Sha256.hmac s mac ciphertext).take 10

def material (s : Sha256.Ops B W) (salt dh : List B) : List B :=
  TlsKdf.expandFast s (TlsKdf.extract s salt dh) [] 96

/-- MESSAGE=2; default content hint is absent and no group ID is supplied. -/
def usmc (a : ByteAuth.Ops B) (certificate inner : List B) : List B :=
  [a.const 8,a.const 2] ++ Serialization.bytesField a 18 certificate ++ Serialization.bytesField a 26 inner

def sealCore (o : Aes.Ops B) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner : List B) : List B :=
  let recipient := a.const 5 :: recipientPublic
  let ephemeral := a.const 5 :: ephemeralPublic
  let sender := a.const 5 :: senderPublic
  let first := material s ((TlsKdf.ascii "UnidentifiedDelivery").map s.byteConst ++ recipient ++ ephemeral) ephemeralDh
  let encryptedStatic := encrypt o s ((first.drop 32).take 32) ((first.drop 64).take 32) sender
  let second := material s (first.take 32 ++ encryptedStatic) staticDh
  let encryptedMessage := encrypt o s ((second.drop 32).take 32) ((second.drop 64).take 32) (usmc a certificate inner)
  a.const 17 :: (Serialization.bytesField a 10 ephemeral ++
    Serialization.bytesField a 18 encryptedStatic ++ Serialization.bytesField a 26 encryptedMessage)

def sealChecked (o : Aes.Ops B) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner : List B) : Option (List B) :=
  if recipientPublic.length=32 ∧ ephemeralPublic.length=32 ∧ senderPublic.length=32 ∧
      ephemeralDh.length=32 ∧ staticDh.length=32 ∧ 0<certificate.length ∧ certificate.length≤1024 ∧
      0<inner.length ∧ inner.length≤4096 then
    some (sealCore o s a recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner)
  else none

def agreementMask (a : ByteAuth.Ops B) (ephemeralDh staticDh : List B) : B :=
  a.and (a.not (ByteAuth.equalMask a ephemeralDh (List.replicate 32 (a.const 0))))
    (a.not (ByteAuth.equalMask a staticDh (List.replicate 32 (a.const 0))))

/-- Secret computed agreement rejection, rather than a supplied validity flag. -/
def privateSeal (o : Aes.Ops B) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner : List B) : List B :=
  let status := agreementMask a ephemeralDh staticDh
  status :: ByteAuth.release a status
    (sealCore o s a recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner)

/-- Bind computed sender public key to the already retained session identity. -/
def boundSeal (o : Aes.Ops B) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner expectedSender : List B) : List B :=
  let status := a.and (agreementMask a ephemeralDh staticDh) (ByteAuth.equalMask a senderPublic expectedSender)
  status :: ByteAuth.release a status
    (sealCore o s a recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner)

section Refinement
variable {o : Aes.Ops B} {o' : Aes.Ops B'} {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'}
  {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} {fw : W → W'}
  (ho : Aes.Hom o o' f) (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)
include ho

theorem counter_map (n : Nat) : (counter o n).map f = counter o' n := by
  simp [counter,List.map_map,ho.const]

theorem ctrLoop_map (expanded : List B) (n index : Nat) (plain : List B) :
    (ctrLoop o expanded n index plain).map f = ctrLoop o' (expanded.map f) n index (plain.map f) := by
  induction n generalizing index plain with
  | zero => rfl
  | succ n ih =>
      simp only [ctrLoop,List.map_append,ih,List.map_drop]
      congr 1
      rw [List.map_zipWith]
      have stream := Aes.encryptExpanded_map ho 14 expanded (counter o index)
      rw [counter_map ho] at stream
      rw [←stream,←List.map_take]
      rw [List.zipWith_map]
      simp only [ho.xor]

theorem ctr_map (key plain : List B) : (ctr o key plain).map f = ctr o' (key.map f) (plain.map f) := by
  simp [ctr,ctrLoop_map ho,Aes.expandKey_map ho]
include hs

theorem encrypt_map (cipher mac plain : List B) :
    (encrypt o s cipher mac plain).map f = encrypt o' s' (cipher.map f) (mac.map f) (plain.map f) := by
  simp [encrypt,ctr_map ho,Sha256.hmac_map hs]
omit ho in
theorem material_map (salt dh : List B) :
    (material s salt dh).map f = material s' (salt.map f) (dh.map f) := by
  simp only [material,TlsKdf.expandFast_correct]
  rw [TlsKdf.expandCore_map hs,TlsKdf.extract_map hs];rfl
include ha
omit ho hs in
theorem usmc_map (certificate inner : List B) :
    (usmc a certificate inner).map f = usmc a' (certificate.map f) (inner.map f) := by
  simp [usmc,Serialization.bytesField_map ha,ha.const]

theorem seal_map (recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner : List B) :
    (sealCore o s a recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner).map f =
      sealCore o' s' a' (recipientPublic.map f) (ephemeralPublic.map f) (senderPublic.map f)
        (ephemeralDh.map f) (staticDh.map f) (certificate.map f) (inner.map f) := by
  simp only [sealCore,List.map_cons,List.map_append,List.map_nil,ha.const,Serialization.bytesField_map ha,
    encrypt_map ho hs,List.map_take,List.map_drop,material_map hs,usmc_map ha,List.map_map,Function.comp_def,hs.byteConst]

theorem sealChecked_map (recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner : List B) :
    (sealChecked o s a recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner).map (List.map f) =
      sealChecked o' s' a' (recipientPublic.map f) (ephemeralPublic.map f) (senderPublic.map f)
        (ephemeralDh.map f) (staticDh.map f) (certificate.map f) (inner.map f) := by
  simp only [sealChecked,List.length_map]
  split <;> simp [seal_map ho hs ha]
omit ho hs in
theorem agreementMask_map (ephemeralDh staticDh : List B) :
    f (agreementMask a ephemeralDh staticDh) = agreementMask a' (ephemeralDh.map f) (staticDh.map f) := by
  simp only [agreementMask,ha.and,ha.not,ByteAuth.equalMask_map ha,List.map_replicate,ha.const]

theorem privateSeal_map (recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner : List B) :
    (privateSeal o s a recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner).map f =
      privateSeal o' s' a' (recipientPublic.map f) (ephemeralPublic.map f) (senderPublic.map f)
        (ephemeralDh.map f) (staticDh.map f) (certificate.map f) (inner.map f) := by
  simp only [privateSeal,List.map_cons,agreementMask_map ha,ByteAuth.release_map ha,seal_map ho hs ha]

theorem boundSeal_map (recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner expectedSender : List B) :
    (boundSeal o s a recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner expectedSender).map f =
      boundSeal o' s' a' (recipientPublic.map f) (ephemeralPublic.map f) (senderPublic.map f)
        (ephemeralDh.map f) (staticDh.map f) (certificate.map f) (inner.map f) (expectedSender.map f) := by
  simp only [boundSeal,List.map_cons,ha.and,agreementMask_map ha,ByteAuth.equalMask_map ha,
    ByteAuth.release_map ha,seal_map ho hs ha]

end Refinement

theorem compiled_seal_correct (recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (sealCore Aes.symbolic Sha256.symbolic ByteAuth.symbolic recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (sealCore Aes.symbolic Sha256.symbolic ByteAuth.symbolic recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
      (sealCore Aes.symbolic Sha256.symbolic ByteAuth.symbolic recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner))).vec.get index hi)) =
      (ByteCircuit.joinValue (sealCore Aes.concrete Sha256.concrete ByteAuth.concrete
        (recipientPublic.map (BVExpr.eval assign)) (ephemeralPublic.map (BVExpr.eval assign))
        (senderPublic.map (BVExpr.eval assign)) (ephemeralDh.map (BVExpr.eval assign))
        (staticDh.map (BVExpr.eval assign)) (certificate.map (BVExpr.eval assign)) (inner.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,seal_map (Aes.evaluationHom assign) (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]

theorem compiled_privateSeal_correct (recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (privateSeal Aes.symbolic Sha256.symbolic ByteAuth.symbolic recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (privateSeal Aes.symbolic Sha256.symbolic ByteAuth.symbolic recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
      (privateSeal Aes.symbolic Sha256.symbolic ByteAuth.symbolic recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner))).vec.get index hi)) =
      (ByteCircuit.joinValue (privateSeal Aes.concrete Sha256.concrete ByteAuth.concrete
        (recipientPublic.map (BVExpr.eval assign)) (ephemeralPublic.map (BVExpr.eval assign))
        (senderPublic.map (BVExpr.eval assign)) (ephemeralDh.map (BVExpr.eval assign))
        (staticDh.map (BVExpr.eval assign)) (certificate.map (BVExpr.eval assign)) (inner.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,privateSeal_map (Aes.evaluationHom assign) (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]
theorem compiled_boundSeal_correct (recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner expectedSender : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (boundSeal Aes.symbolic Sha256.symbolic ByteAuth.symbolic recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner expectedSender).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (boundSeal Aes.symbolic Sha256.symbolic ByteAuth.symbolic recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner expectedSender))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
      (boundSeal Aes.symbolic Sha256.symbolic ByteAuth.symbolic recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner expectedSender))).vec.get index hi)) =
      (ByteCircuit.joinValue (boundSeal Aes.concrete Sha256.concrete ByteAuth.concrete
        (recipientPublic.map (BVExpr.eval assign)) (ephemeralPublic.map (BVExpr.eval assign))
        (senderPublic.map (BVExpr.eval assign)) (ephemeralDh.map (BVExpr.eval assign))
        (staticDh.map (BVExpr.eval assign)) (certificate.map (BVExpr.eval assign)) (inner.map (BVExpr.eval assign)) (expectedSender.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,boundSeal_map (Aes.evaluationHom assign) (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]
end TlsMpc.Signal.SealedSenderV1
