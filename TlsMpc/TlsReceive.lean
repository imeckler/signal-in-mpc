import TlsMpc.TlsRecord
import TlsMpc.TlsInnerParallel

/-!
Receive one complete AES-128-GCM TLSCiphertext record. The received header is
both authenticated as AAD and compared with its required TLS 1.3 encoding.
The inner parser removes zero padding and validates the protected type.
All outputs stay secret: acceptance, type, two-byte content length, then a
fixed-size content buffer. Any header, tag or inner-format failure zeros all
outputs. Public record length is circuit shape, not a decrypted length.

This bounded record function does not authenticate a handshake, authorize a
content type for the current connection state, reserve sequence numbers, or
enforce negotiated record limits and per-key usage limits.
-/

namespace TlsMpc.TlsReceive
open Std.Tactic.BVDecide

def releaseOpened (a : ByteAuth.Ops B) (headerValid : B) (opened : GcmOpen.Opened B) : List B :=
  ByteAuth.release a (a.and headerValid opened.accepted) (TlsInnerParallel.decode a opened.plaintext)

def openParts (g : Gcm.Ops B W) (a : ByteAuth.Ops B)
    (key iv sequence receivedHeader ciphertext receivedTag : List B) : List B :=
  let opened := GcmOpen.openCore g a key (TlsRecord.nonce g iv sequence)
    receivedHeader ciphertext receivedTag
  let headerValid := ByteAuth.equalMask a receivedHeader (TlsRecord.header g (ciphertext.length + 16))
  releaseOpened a headerValid opened

def ciphertext (wire : List B) : List B := (wire.drop 5).take (wire.length - 21)

def openCore (g : Gcm.Ops B W) (a : ByteAuth.Ops B)
    (key iv sequence wire : List B) : List B :=
  openParts g a key iv sequence (wire.take 5) (ciphertext wire) (wire.drop (wire.length - 16))

def openChecked (g : Gcm.Ops B W) (a : ByteAuth.Ops B)
    (key iv sequence wire : List B) : Option (List B) :=
  if key.length = 16 ∧ iv.length = 12 ∧ sequence.length = 8 ∧
      22 ≤ wire.length ∧ wire.length ≤ 16406 then
    some (openCore g a key iv sequence wire)
  else none

def partsSpec (key iv sequence receivedHeader ciphertext receivedTag : List (BitVec 8)) : List (BitVec 8) :=
  let nonce := TlsRecord.nonce Gcm.concrete iv sequence
  let prepared := Gcm.prepare Gcm.concrete key
  if receivedHeader = TlsRecord.header Gcm.concrete (ciphertext.length + 16) then
    if Gcm.tag Gcm.concrete prepared nonce receivedHeader ciphertext = receivedTag then
      TlsInner.spec (Gcm.ctr Gcm.concrete prepared.expanded nonce ciphertext)
    else List.replicate (ciphertext.length + 4) 0
  else List.replicate (ciphertext.length + 4) 0

def spec (key iv sequence wire : List (BitVec 8)) : List (BitVec 8) :=
  partsSpec key iv sequence (wire.take 5) (ciphertext wire) (wire.drop (wire.length - 16))

section Refinement
variable {g : Gcm.Ops B W} {g' : Gcm.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {fb : B → B'} {fw : W → W'} (hg : Gcm.Hom g g' fb fw) (ha : ByteAuth.Hom a a' fb)
include ha

theorem releaseOpened_map (headerValid : B) (opened : GcmOpen.Opened B) :
    (releaseOpened a headerValid opened).map fb = releaseOpened a' (fb headerValid) (opened.map fb) := by
  simp [releaseOpened, ByteAuth.release_map ha, ha.and, TlsInnerParallel.decode_map ha, GcmOpen.Opened.map]

include hg

theorem openParts_map (key iv sequence receivedHeader ciphertext receivedTag : List B) :
    (openParts g a key iv sequence receivedHeader ciphertext receivedTag).map fb =
      openParts g' a' (key.map fb) (iv.map fb) (sequence.map fb) (receivedHeader.map fb)
        (ciphertext.map fb) (receivedTag.map fb) := by
  simp only [openParts, releaseOpened_map ha, ByteAuth.equalMask_map ha,
    TlsRecord.header_map hg, GcmOpen.openCore_map hg ha, TlsRecord.nonce_map hg, List.length_map]

theorem openCore_map (key iv sequence wire : List B) :
    (openCore g a key iv sequence wire).map fb =
      openCore g' a' (key.map fb) (iv.map fb) (sequence.map fb) (wire.map fb) := by
  simp only [openCore, openParts_map hg ha, ciphertext, List.map_take, List.map_drop, List.length_map]

theorem openChecked_map (key iv sequence wire : List B) :
    (openChecked g a key iv sequence wire).map (List.map fb) =
      openChecked g' a' (key.map fb) (iv.map fb) (sequence.map fb) (wire.map fb) := by
  simp only [openChecked, List.length_map]
  split <;> simp_all [openCore_map hg ha]

end Refinement

theorem openParts_length (g : Gcm.Ops B W) (a : ByteAuth.Ops B)
    (key iv sequence receivedHeader ciphertext receivedTag : List B) (hk : key.length = 16) :
    (openParts g a key iv sequence receivedHeader ciphertext receivedTag).length = ciphertext.length + 4 := by
  simp only [openParts, releaseOpened, ByteAuth.release, List.length_map, TlsInnerParallel.decode_length,
    GcmOpen.openCore]
  rw [Gcm.ctr_length g _ _ _ (Gcm.prepared_length g key hk)]

theorem openParts_correct (key iv sequence receivedHeader ciphertext receivedTag : List (BitVec 8))
    (hk : key.length = 16) :
    openParts Gcm.concrete ByteAuth.concrete key iv sequence receivedHeader ciphertext receivedTag =
      partsSpec key iv sequence receivedHeader ciphertext receivedTag := by
  rw [openParts, GcmOpen.openCore_concrete_correct _ _ _ _ _ hk, ByteAuth.equalMask_value]
  have hl := Gcm.ctr_length Gcm.concrete
    (Gcm.prepare Gcm.concrete key).expanded (TlsRecord.nonce Gcm.concrete iv sequence) ciphertext
    (Gcm.prepared_length Gcm.concrete key hk)
  unfold GcmOpen.spec partsSpec
  by_cases hh : receivedHeader = TlsRecord.header Gcm.concrete (ciphertext.length + 16) <;>
    by_cases ht : Gcm.tag Gcm.concrete (Gcm.prepare Gcm.concrete key)
      (TlsRecord.nonce Gcm.concrete iv sequence) receivedHeader ciphertext = receivedTag <;>
    simp only [ht, ↓reduceIte]
  all_goals simp only [hh, ↓reduceIte, releaseOpened]
  · change ByteAuth.release ByteAuth.concrete 255 _ = _
    rw [ByteAuth.release_accept, TlsInnerParallel.decode_spec]
  · change ByteAuth.release ByteAuth.concrete 0 _ = _
    rw [ByteAuth.release_reject, TlsInnerParallel.decode_length, List.length_replicate]
  · change ByteAuth.release ByteAuth.concrete 0 _ = _
    rw [ByteAuth.release_reject, TlsInnerParallel.decode_length, hl]
  · change ByteAuth.release ByteAuth.concrete 0 _ = _
    rw [ByteAuth.release_reject, TlsInnerParallel.decode_length, List.length_replicate]

theorem openCore_correct (key iv sequence wire : List (BitVec 8)) (hk : key.length = 16) :
    openCore Gcm.concrete ByteAuth.concrete key iv sequence wire = spec key iv sequence wire :=
  openParts_correct _ _ _ _ _ _ hk

theorem ciphertext_length (wire : List B) : (ciphertext wire).length = wire.length - 21 := by
  simp only [ciphertext, List.length_take, List.length_drop]
  omega

theorem openCore_length (g : Gcm.Ops B W) (a : ByteAuth.Ops B)
    (key iv sequence wire : List B) (hk : key.length = 16) :
    (openCore g a key iv sequence wire).length = wire.length - 21 + 4 := by
  rw [openCore, openParts_length g a _ _ _ _ _ _ hk, ciphertext_length]

theorem openChecked_correct (key iv sequence wire : List (BitVec 8)) :
    openChecked Gcm.concrete ByteAuth.concrete key iv sequence wire =
      if key.length = 16 ∧ iv.length = 12 ∧ sequence.length = 8 ∧
          22 ≤ wire.length ∧ wire.length ≤ 16406 then
        some (spec key iv sequence wire)
      else none := by
  unfold openChecked
  split
  · rename_i valid
    rw [openCore_correct _ _ _ _ valid.1]
  · rfl

theorem bad_header_zero (key iv sequence receivedHeader ciphertext receivedTag : List (BitVec 8))
    (hk : key.length = 16)
    (bad : receivedHeader ≠ TlsRecord.header Gcm.concrete (ciphertext.length + 16)) :
    openParts Gcm.concrete ByteAuth.concrete key iv sequence receivedHeader ciphertext receivedTag =
      List.replicate (ciphertext.length + 4) 0 := by
  rw [openParts_correct _ _ _ _ _ _ hk]
  simp only [partsSpec, if_neg bad]

theorem bad_tag_zero (key iv sequence receivedHeader ciphertext receivedTag : List (BitVec 8))
    (hk : key.length = 16)
    (bad : Gcm.tag Gcm.concrete (Gcm.prepare Gcm.concrete key)
      (TlsRecord.nonce Gcm.concrete iv sequence) receivedHeader ciphertext ≠ receivedTag) :
    openParts Gcm.concrete ByteAuth.concrete key iv sequence receivedHeader ciphertext receivedTag =
      List.replicate (ciphertext.length + 4) 0 := by
  rw [openParts_correct _ _ _ _ _ _ hk]
  simp only [partsSpec, if_neg bad, ite_self]

theorem compiled_openCore_correct (key iv sequence wire : List (BVExpr 8))
    (hk : key.length = 16) (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (openCore Gcm.symbolic ByteAuth.symbolic key iv sequence wire).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile
        (ByteCircuit.joinExpr (openCore Gcm.symbolic ByteAuth.symbolic key iv sequence wire))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile
        (ByteCircuit.joinExpr (openCore Gcm.symbolic ByteAuth.symbolic key iv sequence wire))).vec.get index hi)) =
    (ByteCircuit.joinValue (spec (key.map (BVExpr.eval assign)) (iv.map (BVExpr.eval assign))
      (sequence.map (BVExpr.eval assign)) (wire.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,
    openCore_map (Gcm.evaluationHom assign) (ByteAuth.evaluationHom assign),
    openCore_correct _ _ _ _ (by simpa using hk)]

end TlsMpc.TlsReceive
