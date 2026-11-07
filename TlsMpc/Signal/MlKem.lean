import TlsMpc.Signal.MlKemPke

/-! ML-KEM and pinned libcrux Kyber CCA composition, using the bounded secret
PKE sampler. Ciphertext equality selects the implicit-rejection secret without
revealing validity. The sole outer failure status records matrix-budget
exhaustion, and gates all outputs. Valid-sized generated keys are the input
precondition; typed Signal wrappers and native entropy provisioning are separate.
The pinned Kyber rejection path applies its KDF to SHAKE256(z || ciphertext),
matching this libcrux version rather than assuming a different Kyber API. -/
namespace TlsMpc.Signal.MlKem
open Std.Tactic.BVDecide

def kdf (k : Keccak.Ops B K) (kyber : Bool) (secret ciphertext : List B) : List B :=
  if kyber then Keccak.shake256 k 32 (secret++Keccak.sha3_256 k ciphertext) else secret

def keygen (r : MlKemArithmetic.Ops W) (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (o : Word64.Ops B O) (k : Keccak.Ops B K)
    (rank eta pairs : Nat) (kyber : Bool) (seed : List B) : MlKemPke.Ciphertext B :=
  let pair := MlKemPke.keygen r s a o k rank eta pairs kyber (seed.take 32)
  let secret := pair.secretKey++pair.publicKey++Keccak.sha3_256 k pair.publicKey++(seed.drop 32).take 32
  ⟨pair.success,secret++pair.publicKey⟩

def encapsulate (r : MlKemArithmetic.Ops W) (c : MlKemEncoding.Ops W) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (o : Word64.Ops B O) (k : Keccak.Ops B K) (rank eta du dv pairs : Nat) (kyber : Bool)
    (publicKey entropy : List B) : MlKemPke.Ciphertext B :=
  let message := if kyber then Keccak.sha3_256 k entropy else entropy
  let expanded := Keccak.sha3_512 k (message++Keccak.sha3_256 k publicKey)
  let encrypted := MlKemPke.encrypt r c s a o k rank eta du dv pairs publicKey message (expanded.drop 32)
  ⟨encrypted.success,encrypted.bytes++kdf k kyber (expanded.take 32) encrypted.bytes⟩

def decapsulate (r : MlKemArithmetic.Ops W) (c : MlKemEncoding.Ops W) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (o : Word64.Ops B O) (k : Keccak.Ops B K) (rank eta du dv pairs : Nat) (kyber : Bool)
    (secretKey ciphertext : List B) : MlKemPke.Ciphertext B :=
  let cpaSecret := secretKey.take (384*rank)
  let publicKey := (secretKey.drop (384*rank)).take (384*rank+32)
  let publicHash := (secretKey.drop (768*rank+32)).take 32
  let z := (secretKey.drop (768*rank+64)).take 32
  let message := MlKemPke.decrypt r c s a rank du dv cpaSecret ciphertext
  let expanded := Keccak.sha3_512 k (message++publicHash)
  let expected := MlKemPke.encrypt r c s a o k rank eta du dv pairs publicKey message (expanded.drop 32)
  let equal := ByteAuth.equalMask a ciphertext expected.bytes
  let candidate := kdf k kyber (expanded.take 32) ciphertext
  let rejection := kdf k kyber (Keccak.shake256 k 32 (z++ciphertext)) ciphertext
  ⟨expected.success,List.zipWith (Unpad.chooseByte a equal) candidate rejection⟩

inductive Operation where
  | keygen | encapsulate | decapsulate
  deriving BEq

def run (r : MlKemArithmetic.Ops W) (c : MlKemEncoding.Ops W) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (o : Word64.Ops B O) (k : Keccak.Ops B K) (rank eta du dv pairs : Nat) (kyber : Bool)
    (operation : Operation) (raw : List B) : List B :=
  let result := match operation with
    | .keygen => keygen r s a o k rank eta pairs kyber raw
    | .encapsulate => encapsulate r c s a o k rank eta du dv pairs kyber (raw.take (384*rank+32)) (raw.drop (384*rank+32))
    | .decapsulate => decapsulate r c s a o k rank eta du dv pairs kyber (raw.take (768*rank+96)) (raw.drop (768*rank+96))
  result.success :: result.bytes.map (a.and result.success)

section
variable {r : MlKemArithmetic.Ops W} {r' : MlKemArithmetic.Ops W'} {c : MlKemEncoding.Ops W} {c' : MlKemEncoding.Ops W'}
  {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {o : Word64.Ops B O} {o' : Word64.Ops B' O'} {k : Keccak.Ops B K} {k' : Keccak.Ops B' K'}
  {f : B → B'} {g : W → W'} {go : O → O'} {gk : K → K'}
  (hr : MlKemArithmetic.Hom r r' g) (hc : MlKemEncoding.Hom c c' g)
  (hs : Sha256.Hom s s' f g) (ha : ByteAuth.Hom a a' f)
  (ho : Word64.Hom o o' f go) (hk : Keccak.Hom k k' f gk)
include hk in
theorem kdf_map (kyber : Bool) (secret ciphertext : List B) :
    (kdf k kyber secret ciphertext).map f = kdf k' kyber (secret.map f) (ciphertext.map f) := by
  cases kyber <;> simp only [kdf,Bool.false_eq_true,↓reduceIte,Keccak.shake256,Keccak.sha3_256,Keccak.hash_map hk,List.map_append]
include hr hs ha ho hk in
theorem keygen_map (rank eta pairs : Nat) (kyber : Bool) (seed : List B) :
    (keygen r s a o k rank eta pairs kyber seed).map f = keygen r' s' a' o' k' rank eta pairs kyber (seed.map f) := by
  simp only [keygen,←List.map_take,←MlKemPke.keygen_map hr hs ha ho hk,MlKemPke.KeyPair.map,MlKemPke.Ciphertext.map,
    List.map_append,Keccak.sha3_256,Keccak.hash_map hk,List.map_take,List.map_drop]
  simp only [←List.map_take,←MlKemPke.keygen_map hr hs ha ho hk,MlKemPke.KeyPair.map]
include hr hc hs ha ho hk in
theorem encapsulate_map (rank eta du dv pairs : Nat) (kyber : Bool) (publicKey entropy : List B) :
    (encapsulate r c s a o k rank eta du dv pairs kyber publicKey entropy).map f =
      encapsulate r' c' s' a' o' k' rank eta du dv pairs kyber (publicKey.map f) (entropy.map f) := by
  cases kyber <;> simp only [encapsulate,Bool.false_eq_true,↓reduceIte,MlKemPke.Ciphertext.map,List.map_append,kdf_map hk,
    Keccak.sha3_512,Keccak.sha3_256,Keccak.hash_map hk,List.map_take,List.map_drop]
  all_goals simp only [←Keccak.hash_map hk,←List.map_append,←List.map_drop,
    ←MlKemPke.encrypt_map hr hc hs ha ho hk,MlKemPke.Ciphertext.map,List.map_take]
include hr hc hs ha ho hk in
theorem decapsulate_map (rank eta du dv pairs : Nat) (kyber : Bool) (secretKey ciphertext : List B) :
    (decapsulate r c s a o k rank eta du dv pairs kyber secretKey ciphertext).map f =
      decapsulate r' c' s' a' o' k' rank eta du dv pairs kyber (secretKey.map f) (ciphertext.map f) := by
  simp only [decapsulate,MlKemPke.Ciphertext.map,List.map_zipWith,List.zipWith_map_left,List.zipWith_map_right,
    Unpad.chooseByte_map ha,ByteAuth.equalMask_map ha]
  simp only [←List.map_take,←List.map_drop,←MlKemPke.decrypt_map hr hc hs ha,←List.map_append,
    ←Keccak.hash_map hk,Keccak.sha3_512,Keccak.sha3_256,Keccak.shake256,
    ←MlKemPke.encrypt_map hr hc hs ha ho hk,MlKemPke.Ciphertext.map]
  simp only [←kdf_map hk,List.zipWith_map_left,List.zipWith_map_right]
include hr hc hs ha ho hk in
theorem run_map (rank eta du dv pairs : Nat) (kyber : Bool) (operation : Operation) (raw : List B) :
    (run r c s a o k rank eta du dv pairs kyber operation raw).map f =
      run r' c' s' a' o' k' rank eta du dv pairs kyber operation (raw.map f) := by
  cases operation
  · simp only [run,←keygen_map hr hs ha ho hk,MlKemPke.Ciphertext.map,List.map_cons,List.map_map,Function.comp_def,ha.and]
  · simp only [run,←List.map_take,←List.map_drop,←encapsulate_map hr hc hs ha ho hk,MlKemPke.Ciphertext.map,List.map_cons,List.map_map,Function.comp_def,ha.and]
  · simp only [run,←List.map_take,←List.map_drop,←decapsulate_map hr hc hs ha ho hk,MlKemPke.Ciphertext.map,List.map_cons,List.map_map,Function.comp_def,ha.and]
end
theorem compiled_run_correct (rank eta du dv pairs : Nat) (kyber : Bool) (operation : Operation)
    (raw : List (BVExpr 8)) (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8*(run MlKemArithmetic.symbolic MlKemEncoding.symbolic Sha256.symbolic ByteAuth.symbolic Word64.symbolic Keccak.symbolic rank eta du dv pairs kyber operation raw).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (run MlKemArithmetic.symbolic MlKemEncoding.symbolic Sha256.symbolic ByteAuth.symbolic Word64.symbolic Keccak.symbolic rank eta du dv pairs kyber operation raw))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (run MlKemArithmetic.symbolic MlKemEncoding.symbolic Sha256.symbolic ByteAuth.symbolic Word64.symbolic Keccak.symbolic rank eta du dv pairs kyber operation raw))).vec.get index hi)) =
      (ByteCircuit.joinValue (run MlKemArithmetic.concrete MlKemEncoding.concrete Sha256.concrete ByteAuth.concrete Word64.concrete Keccak.concrete rank eta du dv pairs kyber operation (raw.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,run_map (MlKemArithmetic.evaluationHom assign) (MlKemEncoding.evaluationHom assign)
    (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign) (Word64.evaluationHom assign) (Keccak.evaluationHom assign)]
end TlsMpc.Signal.MlKem
