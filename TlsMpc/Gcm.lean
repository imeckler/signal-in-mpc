import TlsMpc.Aes
import TlsMpc.Ghash

/-!
AES-128-GCM with 96-bit nonces and 128-bit tags, the TLS profile of
NIST SP 800-38D sections 7.1 and 7.2. Lengths and the per-record block counter
are public. Keys, nonces, associated data, contents and tags remain secret.
This module specifies encryption; authenticated opening is added separately.
The checked wrapper validates public shape/length bounds, not nonce uniqueness.
-/

namespace TlsMpc.Gcm
open Std.Tactic.BVDecide

structure Ops (B W : Type) where
  aes : Aes.Ops B
  field : Ghash.Ops W
  pack : List B → W
  unpack : W → List B

def concrete : Ops (BitVec 8) (BitVec 128) :=
  ⟨Aes.concrete, Ghash.concrete, Ghash.packValue, Ghash.unpackValue⟩

def symbolic : Ops (BVExpr 8) (BVExpr 128) :=
  ⟨Aes.symbolic, Ghash.symbolic, Ghash.packExpr, Ghash.unpackExpr⟩

def encodeNat (o : Ops B W) (width value : Nat) : List B :=
  (List.range width).map (fun i => o.aes.const (value / 2 ^ (8 * (width - 1 - i))))

def zeros (o : Ops B W) (n : Nat) : List B := List.replicate n (o.aes.const 0)

structure Prepared (B W : Type) where
  expanded : List B
  hashPowers : List W

def Prepared.map (fb : B → B') (fw : W → W') (p : Prepared B W) : Prepared B' W' :=
  ⟨p.expanded.map fb, p.hashPowers.map fw⟩

def prepare (o : Ops B W) (key : List B) : Prepared B W :=
  let expanded := Aes.expandKey o.aes 4 10 key
  let h := o.pack (Aes.encryptExpanded o.aes 10 expanded (zeros o 16))
  ⟨expanded, Ghash.powers o.field 128 h⟩

def ctrLoop (o : Ops B W) (expanded nonce : List B) : Nat → Nat → List B → List B
  | 0, _, _ => []
  | n + 1, counter, content =>
      let stream := Aes.encryptExpanded o.aes 10 expanded (nonce ++ encodeNat o 4 counter)
      Aes.addRoundKey o.aes (content.take 16) stream ++
        ctrLoop o expanded nonce n (counter + 1) (content.drop 16)

def ctr (o : Ops B W) (expanded nonce content : List B) : List B :=
  ctrLoop o expanded nonce ((content.length + 15) / 16) 2 content

def pad16 (o : Ops B W) (bytes : List B) : List B :=
  bytes ++ zeros o ((16 - bytes.length % 16) % 16)

def blocks (o : Ops B W) (bytes : List B) : List W :=
  (List.range (bytes.length / 16)).map (fun i => o.pack ((bytes.drop (16 * i)).take 16))

def authInput (o : Ops B W) (aad ciphertext : List B) : List W :=
  blocks o (pad16 o aad ++ pad16 o ciphertext ++
    encodeNat o 8 (8 * aad.length) ++ encodeNat o 8 (8 * ciphertext.length))

def tag (o : Ops B W) (prepared : Prepared B W) (nonce aad ciphertext : List B) : List B :=
  let hash := Ghash.foldPrepared o.field prepared.hashPowers (authInput o aad ciphertext) (o.field.const 0)
  let mask := Aes.encryptExpanded o.aes 10 prepared.expanded (nonce ++ encodeNat o 4 1)
  Aes.addRoundKey o.aes (o.unpack hash) mask

structure Sealed (B : Type) where
  ciphertext : List B
  tag : List B

def Sealed.map (f : B → B') (s : Sealed B) : Sealed B' :=
  ⟨s.ciphertext.map f, s.tag.map f⟩

def Sealed.bytes (s : Sealed B) : List B := s.ciphertext ++ s.tag

def sealPrepared (o : Ops B W) (prepared : Prepared B W) (nonce aad content : List B) : Sealed B :=
  let ciphertext := ctr o prepared.expanded nonce content
  ⟨ciphertext, tag o prepared nonce aad ciphertext⟩

def sealCore (o : Ops B W) (key nonce aad content : List B) : Sealed B :=
  sealPrepared o (prepare o key) nonce aad content

/-- The 96-bit nonce must be unique for this key. These checks do not establish
that stateful property. The exporter imposes a smaller public resource cap. -/
def sealChecked (o : Ops B W) (key nonce aad content : List B) : Option (Sealed B) :=
  if key.length = 16 ∧ nonce.length = 12 ∧ aad.length < 2 ^ 61 ∧ content.length ≤ 2 ^ 36 - 32 then
    some (sealCore o key nonce aad content)
  else none

structure Hom (a : Ops B W) (b : Ops B' W') (fb : B → B') (fw : W → W') : Prop where
  aes : Aes.Hom a.aes b.aes fb
  field : Ghash.Hom a.field b.field fw
  pack : ∀ bytes, fw (a.pack bytes) = b.pack (bytes.map fb)
  unpack : ∀ word, (a.unpack word).map fb = b.unpack (fw word)

def evaluationHom (assign : BVExpr.Assignment) :
    Hom symbolic concrete (BVExpr.eval assign) (BVExpr.eval assign) :=
  ⟨Aes.evaluationHom assign, Ghash.evaluationHom assign,
    Ghash.pack_refines assign, Ghash.unpack_refines assign⟩

section Refinement
variable {a : Ops B W} {b : Ops B' W'} {fb : B → B'} {fw : W → W'} (h : Hom a b fb fw)
include h

theorem encodeNat_map (width value : Nat) : (encodeNat a width value).map fb = encodeNat b width value := by
  simp [encodeNat, List.map_map, Function.comp_def, h.aes.const]

theorem zeros_map (n : Nat) : (zeros a n).map fb = zeros b n := by
  simp [zeros, h.aes.const]

theorem prepare_map (key : List B) :
    (prepare a key).map fb fw = prepare b (key.map fb) := by
  simp [prepare, Prepared.map, Ghash.powers_map h.field, h.pack,
    Aes.encryptExpanded_map h.aes, Aes.expandKey_map h.aes, zeros_map h]

theorem ctrLoop_map (expanded nonce : List B) (n counter : Nat) (content : List B) :
    (ctrLoop a expanded nonce n counter content).map fb =
      ctrLoop b (expanded.map fb) (nonce.map fb) n counter (content.map fb) := by
  induction n generalizing counter content with
  | zero => rfl
  | succ n ih =>
      simp [ctrLoop, ih, Aes.addRoundKey_map h.aes, Aes.encryptExpanded_map h.aes, encodeNat_map h]

theorem ctr_map (expanded nonce content : List B) :
    (ctr a expanded nonce content).map fb = ctr b (expanded.map fb) (nonce.map fb) (content.map fb) := by
  simp [ctr, ctrLoop_map h]

theorem pad16_map (bytes : List B) : (pad16 a bytes).map fb = pad16 b (bytes.map fb) := by
  simp [pad16, zeros_map h]

theorem blocks_map (bytes : List B) : (blocks a bytes).map fw = blocks b (bytes.map fb) := by
  simp [blocks, List.map_map, Function.comp_def, h.pack]

theorem authInput_map (aad ciphertext : List B) :
    (authInput a aad ciphertext).map fw = authInput b (aad.map fb) (ciphertext.map fb) := by
  simp [authInput, blocks_map h, pad16_map h, encodeNat_map h]

theorem tag_map (prepared : Prepared B W) (nonce aad ciphertext : List B) :
    (tag a prepared nonce aad ciphertext).map fb =
      tag b (prepared.map fb fw) (nonce.map fb) (aad.map fb) (ciphertext.map fb) := by
  simp [tag, Prepared.map, Aes.addRoundKey_map h.aes, h.unpack,
    Ghash.foldPrepared_map h.field, authInput_map h, h.field.const,
    Aes.encryptExpanded_map h.aes, encodeNat_map h]

theorem sealPrepared_map (prepared : Prepared B W) (nonce aad content : List B) :
    (sealPrepared a prepared nonce aad content).map fb =
      sealPrepared b (prepared.map fb fw) (nonce.map fb) (aad.map fb) (content.map fb) := by
  simp [sealPrepared, Sealed.map, ctr_map h, tag_map h, Prepared.map]

theorem sealCore_map (key nonce aad content : List B) :
    (sealCore a key nonce aad content).map fb =
      sealCore b (key.map fb) (nonce.map fb) (aad.map fb) (content.map fb) := by
  simp [sealCore, sealPrepared_map h, prepare_map h]

theorem sealCore_bytes_map (key nonce aad content : List B) :
    (sealCore a key nonce aad content).bytes.map fb =
      (sealCore b (key.map fb) (nonce.map fb) (aad.map fb) (content.map fb)).bytes := by
  have hm := congrArg Sealed.bytes (sealCore_map h key nonce aad content)
  simpa [Sealed.bytes, Sealed.map] using hm

theorem sealChecked_map (key nonce aad content : List B) :
    (sealChecked a key nonce aad content).map (Sealed.map fb) =
      sealChecked b (key.map fb) (nonce.map fb) (aad.map fb) (content.map fb) := by
  simp only [sealChecked, List.length_map]
  split <;> simp_all [sealCore_map h]

end Refinement

theorem prepared_length (o : Ops B W) (key : List B) (hk : key.length = 16) :
    (prepare o key).expanded.length = 176 := by
  exact Aes.expandKey_length o.aes 4 10 key hk (by decide)

theorem ctrLoop_length (o : Ops B W) (expanded nonce : List B) (n counter : Nat)
    (content : List B) (he : expanded.length = 176) (hc : content.length ≤ 16 * n) :
    (ctrLoop o expanded nonce n counter content).length = content.length := by
  induction n generalizing counter content with
  | zero => simp [ctrLoop]; omega
  | succ n ih =>
      have hd : (content.drop 16).length ≤ 16 * n := by simp only [List.length_drop]; omega
      simp only [ctrLoop, List.length_append, Aes.addRoundKey, List.length_zipWith,
        List.length_take, Aes.encryptExpanded_length o.aes 10 _ _ he,
        ih (counter + 1) (content.drop 16) hd, List.length_drop]
      omega

theorem ctr_length (o : Ops B W) (expanded nonce content : List B)
    (he : expanded.length = 176) : (ctr o expanded nonce content).length = content.length := by
  exact ctrLoop_length o expanded nonce _ _ content he (by omega)

theorem tag_length (o : Ops B W) (prepared : Prepared B W) (nonce aad ciphertext : List B)
    (he : prepared.expanded.length = 176) (hu : ∀ w, (o.unpack w).length = 16) :
    (tag o prepared nonce aad ciphertext).length = 16 := by
  simp only [tag, Aes.addRoundKey, List.length_zipWith, hu,
    Aes.encryptExpanded_length o.aes 10 _ _ he, Nat.min_self]

theorem sealCore_bytes_length (o : Ops B W) (key nonce aad content : List B)
    (hk : key.length = 16) (hu : ∀ w, (o.unpack w).length = 16) :
    (sealCore o key nonce aad content).bytes.length = content.length + 16 := by
  simp only [sealCore, sealPrepared, Sealed.bytes, List.length_append]
  rw [tag_length o _ _ _ _ (prepared_length o key hk) hu,
    ctr_length o _ _ _ (prepared_length o key hk)]

theorem compiled_sealCore_correct (key nonce aad content : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (sealCore symbolic key nonce aad content).bytes.length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile
        (ByteCircuit.joinExpr (sealCore symbolic key nonce aad content).bytes)).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile
        (ByteCircuit.joinExpr (sealCore symbolic key nonce aad content).bytes)).vec.get index hi)) =
    (ByteCircuit.joinValue (sealCore concrete (key.map (BVExpr.eval assign))
      (nonce.map (BVExpr.eval assign)) (aad.map (BVExpr.eval assign))
      (content.map (BVExpr.eval assign))).bytes).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, sealCore_bytes_map (evaluationHom assign)]

end TlsMpc.Gcm
