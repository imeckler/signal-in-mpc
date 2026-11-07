import TlsMpc.Gcm
import TlsMpc.ByteAuth

/-!
Authenticated AES-128-GCM opening, with a fixed-size shared result. The circuit
computes the candidate plaintext but masks every output byte when the tag is
wrong. The first output byte is a secret acceptance mask, 255 or 0. Neither
the mask nor the plaintext is opened here. The direct specification branches
on tag equality; the symbolic implementation has no secret-dependent control.
-/

namespace TlsMpc.GcmOpen
open Std.Tactic.BVDecide

structure Opened (B : Type) where
  accepted : B
  plaintext : List B
  deriving DecidableEq

def Opened.map (f : B → B') (r : Opened B) : Opened B' :=
  ⟨f r.accepted, r.plaintext.map f⟩

def Opened.bytes (r : Opened B) : List B := r.accepted :: r.plaintext

theorem Opened.bytes_map (r : Opened B) (f : B → B') :
    (r.map f).bytes = r.bytes.map f := rfl

def openCore (g : Gcm.Ops B W) (a : ByteAuth.Ops B)
    (key nonce aad ciphertext receivedTag : List B) : Opened B :=
  let prepared := Gcm.prepare g key
  let expected := Gcm.tag g prepared nonce aad ciphertext
  let accepted := ByteAuth.equalMask a expected receivedTag
  let candidate := Gcm.ctr g prepared.expanded nonce ciphertext
  ⟨accepted, ByteAuth.release a accepted candidate⟩

def openChecked (g : Gcm.Ops B W) (a : ByteAuth.Ops B)
    (key nonce aad ciphertext receivedTag : List B) : Option (Opened B) :=
  if key.length = 16 ∧ nonce.length = 12 ∧ receivedTag.length = 16 ∧
      aad.length < 2 ^ 61 ∧ ciphertext.length ≤ 2 ^ 36 - 32 then
    some (openCore g a key nonce aad ciphertext receivedTag)
  else none

/-- Direct success/failure semantics, using a plaintext buffer as long as the
ciphertext even on rejection. Public input lengths are checked separately. -/
def spec (key nonce aad ciphertext receivedTag : List (BitVec 8)) : Opened (BitVec 8) :=
  let prepared := Gcm.prepare Gcm.concrete key
  if Gcm.tag Gcm.concrete prepared nonce aad ciphertext = receivedTag then
    ⟨255, Gcm.ctr Gcm.concrete prepared.expanded nonce ciphertext⟩
  else ⟨0, List.replicate ciphertext.length 0⟩

theorem openCore_concrete_correct (key nonce aad ciphertext receivedTag : List (BitVec 8))
    (hk : key.length = 16) :
    openCore Gcm.concrete ByteAuth.concrete key nonce aad ciphertext receivedTag =
      spec key nonce aad ciphertext receivedTag := by
  simp only [openCore, ByteAuth.equalMask_value, spec]
  split
  · rw [ByteAuth.release_accept]
  · rw [ByteAuth.release_reject,
      Gcm.ctr_length Gcm.concrete _ _ _ (Gcm.prepared_length Gcm.concrete key hk)]

section Refinement
variable {g : Gcm.Ops B W} {g' : Gcm.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {fb : B → B'} {fw : W → W'} (hg : Gcm.Hom g g' fb fw) (ha : ByteAuth.Hom a a' fb)
include hg ha

theorem openCore_map (key nonce aad ciphertext receivedTag : List B) :
    (openCore g a key nonce aad ciphertext receivedTag).map fb =
      openCore g' a' (key.map fb) (nonce.map fb) (aad.map fb)
        (ciphertext.map fb) (receivedTag.map fb) := by
  simp [openCore, Opened.map, ByteAuth.equalMask_map ha, ByteAuth.release_map ha,
    Gcm.tag_map hg, Gcm.ctr_map hg, ← Gcm.prepare_map hg, Gcm.Prepared.map]

theorem openCore_bytes_map (key nonce aad ciphertext receivedTag : List B) :
    (openCore g a key nonce aad ciphertext receivedTag).bytes.map fb =
      (openCore g' a' (key.map fb) (nonce.map fb) (aad.map fb)
        (ciphertext.map fb) (receivedTag.map fb)).bytes := by
  have hm := congrArg Opened.bytes (openCore_map hg ha key nonce aad ciphertext receivedTag)
  simpa [Opened.bytes, Opened.map] using hm

theorem openChecked_map (key nonce aad ciphertext receivedTag : List B) :
    (openChecked g a key nonce aad ciphertext receivedTag).map (Opened.map fb) =
      openChecked g' a' (key.map fb) (nonce.map fb) (aad.map fb)
        (ciphertext.map fb) (receivedTag.map fb) := by
  simp only [openChecked, List.length_map]
  split <;> simp_all [openCore_map hg ha]

end Refinement

theorem rejected_zero (key nonce aad ciphertext receivedTag : List (BitVec 8))
    (hk : key.length = 16)
    (bad : Gcm.tag Gcm.concrete (Gcm.prepare Gcm.concrete key) nonce aad ciphertext ≠ receivedTag) :
    openCore Gcm.concrete ByteAuth.concrete key nonce aad ciphertext receivedTag =
      ⟨0, List.replicate ciphertext.length 0⟩ := by
  rw [openCore_concrete_correct _ _ _ _ _ hk]
  simp only [spec, if_neg bad]

theorem compiled_openCore_correct (key nonce aad ciphertext receivedTag : List (BVExpr 8))
    (hk : key.length = 16) (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (openCore Gcm.symbolic ByteAuth.symbolic key nonce aad ciphertext receivedTag).bytes.length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile
        (ByteCircuit.joinExpr (openCore Gcm.symbolic ByteAuth.symbolic key nonce aad ciphertext receivedTag).bytes)).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile
        (ByteCircuit.joinExpr (openCore Gcm.symbolic ByteAuth.symbolic key nonce aad ciphertext receivedTag).bytes)).vec.get index hi)) =
    (ByteCircuit.joinValue (spec (key.map (BVExpr.eval assign))
      (nonce.map (BVExpr.eval assign)) (aad.map (BVExpr.eval assign))
      (ciphertext.map (BVExpr.eval assign)) (receivedTag.map (BVExpr.eval assign))).bytes).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,
    openCore_bytes_map (Gcm.evaluationHom assign) (ByteAuth.evaluationHom assign),
    openCore_concrete_correct _ _ _ _ _ (by simpa using hk)]

end TlsMpc.GcmOpen
