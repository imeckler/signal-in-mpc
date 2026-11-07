import TlsMpc.Aes

/-!
AES-256-CBC send-path implementation following the pinned libsignal
rust/crypto/src/aes_cbc.rs call shape. The actual RustCrypto padding/AES/CBC
composition remains a separate implementation-reference obligation. The
theorems here establish lowering of this Lean implementation to MPC gates.
Key, IV, plaintext, padded bytes, and ciphertext remain secret throughout.
-/

namespace TlsMpc.Signal.Cbc

open Std.Tactic.BVDecide

def pad (o : Aes.Ops B) (plaintext : List B) : List B :=
  let count := 16 - plaintext.length % 16
  plaintext ++ List.replicate count (o.const count)

def encryptBlocks (o : Aes.Ops B) (expanded : List B) : Nat → List B → List B → List B
  | 0, _, _ => []
  | n + 1, iv, plaintext =>
    let block := Aes.addRoundKey o (plaintext.take 16) iv
    let ciphertext := Aes.encryptExpanded o 14 expanded block
    ciphertext ++ encryptBlocks o expanded n ciphertext (plaintext.drop 16)

def encryptCore (o : Aes.Ops B) (key iv plaintext : List B) : List B :=
  let expanded := Aes.expandKey o 8 14 key
  encryptBlocks o expanded (plaintext.length / 16 + 1) iv (pad o plaintext)

def encrypt (o : Aes.Ops B) (key iv plaintext : List B) : Option (List B) :=
  if key.length = 32 ∧ iv.length = 16 then some (encryptCore o key iv plaintext) else none

theorem pad_map {a : Aes.Ops B} {b : Aes.Ops B'} {f : B → B'}
    (h : Aes.Hom a b f) (plaintext : List B) :
    (pad a plaintext).map f = pad b (plaintext.map f) := by
  simp [pad, h.const]

theorem encryptBlocks_map {a : Aes.Ops B} {b : Aes.Ops B'} {f : B → B'}
    (h : Aes.Hom a b f) (expanded : List B) (n : Nat) (iv plaintext : List B) :
    (encryptBlocks a expanded n iv plaintext).map f =
      encryptBlocks b (expanded.map f) n (iv.map f) (plaintext.map f) := by
  induction n generalizing iv plaintext with
  | zero => rfl
  | succ n ih =>
    simp only [encryptBlocks, List.map_append, Aes.encryptExpanded_map h,
      Aes.addRoundKey_map h, List.map_take, ih, List.map_drop]

theorem encryptCore_map {a : Aes.Ops B} {b : Aes.Ops B'} {f : B → B'}
    (h : Aes.Hom a b f) (key iv plaintext : List B) :
    (encryptCore a key iv plaintext).map f =
      encryptCore b (key.map f) (iv.map f) (plaintext.map f) := by
  simp only [encryptCore, encryptBlocks_map h, Aes.expandKey_map h, pad_map h, List.length_map]

theorem encrypt_map {a : Aes.Ops B} {b : Aes.Ops B'} {f : B → B'}
    (h : Aes.Hom a b f) (key iv plaintext : List B) :
    (encrypt a key iv plaintext).map (List.map f) =
      encrypt b (key.map f) (iv.map f) (plaintext.map f) := by
  simp only [encrypt, List.length_map]
  split <;> simp [encryptCore_map h]

theorem compiled_encryptCore_correct (key iv plaintext : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (encryptCore Aes.symbolic key iv plaintext).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile
        (ByteCircuit.joinExpr (encryptCore Aes.symbolic key iv plaintext))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile
        (ByteCircuit.joinExpr (encryptCore Aes.symbolic key iv plaintext))).vec.get index hi)) =
      (ByteCircuit.joinValue (encryptCore Aes.concrete
        (key.map (BVExpr.eval assign)) (iv.map (BVExpr.eval assign))
        (plaintext.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, encryptCore_map (Aes.evaluationHom assign)]

end TlsMpc.Signal.Cbc
