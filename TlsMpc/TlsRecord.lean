import TlsMpc.GcmOpen
import TlsMpc.TlsLayout

/-!
TLS 1.3 AES-128-GCM record protection, RFC 9846 sections 5.2--5.4.
The key, IV, 64-bit sequence (eight network-order bytes) and contents are
shared. Length, padding and outgoing content type are public circuit shape.
This composes record framing with AEAD; it does not implement a handshake,
durable sequence allocation, key-use limits or incoming inner-content parsing.
-/

namespace TlsMpc.TlsRecord
open Std.Tactic.BVDecide

def nonce (o : Gcm.Ops B W) (iv sequence : List B) : List B :=
  Aes.addRoundKey o.aes iv (Gcm.zeros o 4 ++ sequence)

def header (o : Gcm.Ops B W) (ciphertextBytes : Nat) : List B :=
  [o.aes.const 23, o.aes.const 3, o.aes.const 3] ++ Gcm.encodeNat o 2 ciphertextBytes

def inner (o : Gcm.Ops B W) (content : List B) (kind padding : Nat) : List B :=
  content ++ [o.aes.const kind] ++ Gcm.zeros o padding

def sealCore (o : Gcm.Ops B W) (key iv sequence content : List B) (kind padding : Nat) : List B :=
  let plaintext := inner o content kind padding
  let aad := header o (plaintext.length + 16)
  aad ++ (Gcm.sealCore o key (nonce o iv sequence) aad plaintext).bytes

/-- Public shape checks. A caller must additionally supply a fresh reserved
sequence under this key and enforce its handshake/key-usage state. -/
def sealChecked (o : Gcm.Ops B W) (key iv sequence content : List B) (kind padding : Nat) :
    Option (List B) :=
  if key.length = 16 ∧ iv.length = 12 ∧ sequence.length = 8 ∧
      (kind = 21 ∨ kind = 22 ∨ kind = 23) ∧ (kind = 23 ∨ content.length > 0) ∧
      content.length + 1 + padding ≤ 16385 then
    some (sealCore o key iv sequence content kind padding)
  else none

/-- Open a protected payload under the canonical public TLSCiphertext header.
The caller first checks the received public header equals that encoding and
splits its last sixteen bytes as the tag. On success the secret result is the
entire TLSInnerPlaintext; type/padding validation must precede application use.
-/
def openInner (g : Gcm.Ops B W) (a : ByteAuth.Ops B)
    (key iv sequence ciphertext receivedTag : List B) : GcmOpen.Opened B :=
  GcmOpen.openCore g a key (nonce g iv sequence)
    (header g (ciphertext.length + 16)) ciphertext receivedTag

section Refinement
variable {a : Gcm.Ops B W} {b : Gcm.Ops B' W'} {fb : B → B'} {fw : W → W'} (h : Gcm.Hom a b fb fw)
include h

theorem nonce_map (iv sequence : List B) :
    (nonce a iv sequence).map fb = nonce b (iv.map fb) (sequence.map fb) := by
  simp [nonce, Aes.addRoundKey_map h.aes, Gcm.zeros_map h]

theorem header_map (size : Nat) : (header a size).map fb = header b size := by
  simp [header, Gcm.encodeNat_map h, h.aes.const]

theorem inner_map (content : List B) (kind padding : Nat) :
    (inner a content kind padding).map fb = inner b (content.map fb) kind padding := by
  simp [inner, Gcm.zeros_map h, h.aes.const]

theorem sealCore_map (key iv sequence content : List B) (kind padding : Nat) :
    (sealCore a key iv sequence content kind padding).map fb =
      sealCore b (key.map fb) (iv.map fb) (sequence.map fb) (content.map fb) kind padding := by
  simp [sealCore, Gcm.sealCore_bytes_map h, nonce_map h, header_map h,
    inner, Gcm.zeros, h.aes.const]

theorem sealChecked_map (key iv sequence content : List B) (kind padding : Nat) :
    (sealChecked a key iv sequence content kind padding).map (List.map fb) =
      sealChecked b (key.map fb) (iv.map fb) (sequence.map fb) (content.map fb) kind padding := by
  simp only [sealChecked, List.length_map]
  split <;> simp_all [sealCore_map h]

end Refinement

theorem header_concrete (size : Nat) : header Gcm.concrete size = Tls13.headerBytes size := by
  simp [header, Tls13.headerBytes, Gcm.encodeNat, Gcm.concrete, Aes.concrete, List.range_succ]

theorem sealCore_length (o : Gcm.Ops B W) (key iv sequence content : List B) (kind padding : Nat)
    (hk : key.length = 16) (hu : ∀ w, (o.unpack w).length = 16) :
    (sealCore o key iv sequence content kind padding).length = content.length + padding + 22 := by
  simp [sealCore, Gcm.sealCore_bytes_length o _ _ _ _ hk hu, inner, Gcm.zeros,
    header, Gcm.encodeNat]
  omega

theorem openInner_refines (key iv sequence ciphertext receivedTag : List (BVExpr 8))
    (hk : key.length = 16) (assign : BVExpr.Assignment) :
    (openInner Gcm.symbolic ByteAuth.symbolic key iv sequence ciphertext receivedTag).map (BVExpr.eval assign) =
      GcmOpen.spec (key.map (BVExpr.eval assign))
        (nonce Gcm.concrete (iv.map (BVExpr.eval assign)) (sequence.map (BVExpr.eval assign)))
        (header Gcm.concrete (ciphertext.length + 16))
        (ciphertext.map (BVExpr.eval assign)) (receivedTag.map (BVExpr.eval assign)) := by
  simp only [openInner, GcmOpen.openCore_map (Gcm.evaluationHom assign) (ByteAuth.evaluationHom assign),
    nonce_map (Gcm.evaluationHom assign), header_map (Gcm.evaluationHom assign)]
  exact GcmOpen.openCore_concrete_correct _ _ _ _ _ (by simpa using hk)

theorem compiled_sealCore_correct (key iv sequence content : List (BVExpr 8)) (kind padding : Nat)
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (sealCore Gcm.symbolic key iv sequence content kind padding).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile
        (ByteCircuit.joinExpr (sealCore Gcm.symbolic key iv sequence content kind padding))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile
        (ByteCircuit.joinExpr (sealCore Gcm.symbolic key iv sequence content kind padding))).vec.get index hi)) =
    (ByteCircuit.joinValue (sealCore Gcm.concrete (key.map (BVExpr.eval assign))
      (iv.map (BVExpr.eval assign)) (sequence.map (BVExpr.eval assign))
      (content.map (BVExpr.eval assign)) kind padding)).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, sealCore_map (Gcm.evaluationHom assign)]

theorem compiled_openInner_correct (key iv sequence ciphertext receivedTag : List (BVExpr 8))
    (hk : key.length = 16) (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (openInner Gcm.symbolic ByteAuth.symbolic key iv sequence ciphertext receivedTag).bytes.length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile
        (ByteCircuit.joinExpr (openInner Gcm.symbolic ByteAuth.symbolic key iv sequence ciphertext receivedTag).bytes)).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile
        (ByteCircuit.joinExpr (openInner Gcm.symbolic ByteAuth.symbolic key iv sequence ciphertext receivedTag).bytes)).vec.get index hi)) =
    (ByteCircuit.joinValue (GcmOpen.spec (key.map (BVExpr.eval assign))
      (nonce Gcm.concrete (iv.map (BVExpr.eval assign)) (sequence.map (BVExpr.eval assign)))
      (header Gcm.concrete (ciphertext.length + 16))
      (ciphertext.map (BVExpr.eval assign)) (receivedTag.map (BVExpr.eval assign))).bytes).getLsbD index := by
  have hm := congrArg GcmOpen.Opened.bytes (openInner_refines key iv sequence ciphertext receivedTag hk assign)
  rw [GcmOpen.Opened.bytes_map] at hm
  rw [ByteCircuit.compile_bytes_correct, hm]

end TlsMpc.TlsRecord
