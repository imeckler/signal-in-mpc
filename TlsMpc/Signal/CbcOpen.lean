import TlsMpc.AesInverse
import TlsMpc.Signal.OpenResult

/-! AES256-CBC opening and strict secret PKCS7 decoding. The expanded key is
shared by all blocks. `openCore` checks padding, but message authentication must
be supplied by the composed receive operation before any result is released.
This is verified Lean-to-circuit lowering; complete RustCrypto AES/CBC wrapper
equivalence remains an explicit separate obligation. -/

namespace TlsMpc.Signal.CbcOpen
open Std.Tactic.BVDecide

def xorBlock (o : Aes.Ops B) (block previous : List B) : List B :=
  (List.range 16).map (fun i => o.xor (Aes.get o block i) (Aes.get o previous i))

def decryptBlocks (o : AesInverse.Ops B) (expanded : List B) : Nat → List B → List B → List B
  | 0, _, _ => []
  | n + 1, previous, ciphertext =>
    let block := ciphertext.take 16
    xorBlock o.aes (AesInverse.decryptExpanded o 14 expanded block) previous ++
      decryptBlocks o expanded n block (ciphertext.drop 16)

def decryptCore (o : AesInverse.Ops B) (key iv ciphertext : List B) : List B :=
  let expanded := Aes.expandKey o.aes 8 14 key
  decryptBlocks o expanded (ciphertext.length / 16) iv ciphertext

def openCore (o : AesInverse.Ops B) (a : ByteAuth.Ops B) (key iv ciphertext : List B) : List B :=
  OpenResult.finish a (a.const 255) (decryptCore o key iv ciphertext)

inductive ShapeError where
  | badCiphertextLength
  | badKeyOrIv
  deriving DecidableEq

/-- Public shape checks preserve the pinned wrapper's length-check ordering.
Padding validity is encoded in the shared result, never branched on here. -/
def openChecked (o : AesInverse.Ops B) (a : ByteAuth.Ops B)
    (key iv ciphertext : List B) : Except ShapeError (List B) :=
  if ciphertext.length = 0 ∨ ciphertext.length % 16 ≠ 0 then .error .badCiphertextLength
  else if key.length ≠ 32 ∨ iv.length ≠ 16 then .error .badKeyOrIv
  else .ok (openCore o a key iv ciphertext)

section Refinement
variable {o : AesInverse.Ops B} {o' : AesInverse.Ops B'}
  {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'}
  (ho : AesInverse.Hom o o' f) (ha : ByteAuth.Hom a a' f)

theorem xorBlock_map (h : Aes.Hom o.aes o'.aes f) (block previous : List B) :
    (xorBlock o.aes block previous).map f = xorBlock o'.aes (block.map f) (previous.map f) := by
  simp [xorBlock, List.map_map, Function.comp_def, h.xor, Aes.get_map h]

include ho

theorem decryptBlocks_map (expanded : List B) (n : Nat) (previous ciphertext : List B) :
    (decryptBlocks o expanded n previous ciphertext).map f =
      decryptBlocks o' (expanded.map f) n (previous.map f) (ciphertext.map f) := by
  induction n generalizing previous ciphertext with
  | zero => rfl
  | succ n ih =>
    simp only [decryptBlocks, List.map_append, xorBlock_map ho.aes,
      AesInverse.decryptExpanded_map ho, List.map_take, List.map_drop, ih]

theorem decryptCore_map (key iv ciphertext : List B) :
    (decryptCore o key iv ciphertext).map f =
      decryptCore o' (key.map f) (iv.map f) (ciphertext.map f) := by
  simp only [decryptCore, decryptBlocks_map ho, Aes.expandKey_map ho.aes, List.length_map]

include ha in
theorem openCore_map (key iv ciphertext : List B) :
    (openCore o a key iv ciphertext).map f =
      openCore o' a' (key.map f) (iv.map f) (ciphertext.map f) := by
  simp only [openCore, OpenResult.finish_map ha, ha.const, decryptCore_map ho]

include ha in
theorem openChecked_map (key iv ciphertext : List B) :
    (openChecked o a key iv ciphertext).map (List.map f) =
      openChecked o' a' (key.map f) (iv.map f) (ciphertext.map f) := by
  simp only [openChecked, List.length_map]
  split
  · rfl
  · split
    · rfl
    · simp only [Except.map, openCore_map ho ha]

end Refinement

theorem decryptBlocks_length (o : AesInverse.Ops B) (expanded : List B) (n : Nat)
    (previous ciphertext : List B) :
    (decryptBlocks o expanded n previous ciphertext).length = 16 * n := by
  induction n generalizing previous ciphertext with
  | zero => simp [decryptBlocks]
  | succ n ih => simp [decryptBlocks, xorBlock, ih, Nat.mul_add, Nat.add_comm]

theorem decryptCore_length (o : AesInverse.Ops B) (key iv ciphertext : List B)
    (hc : ciphertext.length % 16 = 0) :
    (decryptCore o key iv ciphertext).length = ciphertext.length := by
  rw [decryptCore, decryptBlocks_length]
  omega

theorem openCore_length (o : AesInverse.Ops B) (a : ByteAuth.Ops B) (key iv ciphertext : List B)
    (hc : ciphertext.length % 16 = 0) (hn : 0 < ciphertext.length) :
    (openCore o a key iv ciphertext).length = 9 + ciphertext.length := by
  rw [openCore, OpenResult.finish_length, decryptCore_length o _ _ _ hc]
  rw [decryptCore_length o _ _ _ hc]
  omega

theorem compiled_openCore_correct (key iv ciphertext : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (openCore AesInverse.symbolic ByteAuth.symbolic key iv ciphertext).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile
        (ByteCircuit.joinExpr (openCore AesInverse.symbolic ByteAuth.symbolic key iv ciphertext))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile
        (ByteCircuit.joinExpr (openCore AesInverse.symbolic ByteAuth.symbolic key iv ciphertext))).vec.get index hi)) =
      (ByteCircuit.joinValue (openCore AesInverse.concrete ByteAuth.concrete
        (key.map (BVExpr.eval assign)) (iv.map (BVExpr.eval assign))
        (ciphertext.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,
    openCore_map (AesInverse.evaluationHom assign) (ByteAuth.evaluationHom assign)]

end TlsMpc.Signal.CbcOpen
