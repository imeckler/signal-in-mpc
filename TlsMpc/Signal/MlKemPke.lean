import TlsMpc.Signal.MlKemEncoding
import TlsMpc.Signal.MlKemSample

/-! Shared bounded ML-KEM/Kyber IND-CPA polynomial composition. Matrix
sampling may abort with a shared flag; callers must gate serialized output.
Public parameters are rank, eta and compression widths. CCA rejection,
key validation and typed Signal serialization are separate compositions. -/
namespace TlsMpc.Signal.MlKemPke
open Std.Tactic.BVDecide
abbrev Poly (W : Type) := List W

def zero (s : Sha256.Ops B W) : Poly W := List.replicate 256 (s.wordConst 0)
def add (r : MlKemArithmetic.Ops W) (s : Sha256.Ops B W) (x y : Poly W) : Poly W :=
  List.zipWith (MlKemArithmetic.addMod r s) x y
def sub (r : MlKemArithmetic.Ops W) (s : Sha256.Ops B W) (x y : Poly W) : Poly W :=
  List.zipWith (MlKemArithmetic.subMod r s) x y
def sum (r : MlKemArithmetic.Ops W) (s : Sha256.Ops B W) (polys : List (Poly W)) : Poly W :=
  polys.foldl (add r s) (zero s)
def dot (r : MlKemArithmetic.Ops W) (s : Sha256.Ops B W) (rank : Nat) (left right : Nat → Poly W) : Poly W :=
  sum r s ((List.range rank).map (fun i => MlKemNtt.baseMultiply r s (left i) (right i)))
def noise (r : MlKemArithmetic.Ops W) (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (k : Keccak.Ops B K)
    (eta : Nat) (seed : List B) (nonce : Nat) : Poly W :=
  MlKemNtt.decodePoly s a (MlKemArithmetic.noise r s a k eta (seed++[a.const nonce]))
def decode (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (rank : Nat) (raw : List B) : Nat → Poly W :=
  fun i => MlKemEncoding.decode s a 12 256 ((raw.drop (384*(i%rank))).take 384)
def encode (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (rank : Nat) (polys : Nat → Poly W) : List B :=
  (List.range rank).flatMap (fun i => MlKemEncoding.encode s a 12 256 (polys i))

structure Matrix (B W : Type) where
  success : B
  entries : Nat → Nat → Poly W

def matrix (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (o : Word64.Ops B O) (k : Keccak.Ops B K)
    (rank pairs : Nat) (transpose : Bool) (rho : List B) : Matrix B W :=
  let rows := (List.range (rank*rank)).map (fun n =>
    let i := n/rank
    let j := n%rank
    MlKemSample.matrix o a k 256 pairs (rho++(if transpose then [a.const i,a.const j] else [a.const j,a.const i])))
  let getRow := fun i j => rows[i*rank+j]?.getD []
  ⟨rows.foldl (fun flag row => a.and flag (OpenResult.get a row 0)) (a.const 255),
   fun i j => MlKemNtt.decodePoly s a ((getRow i j).drop 1)⟩
structure KeyPair (B : Type) where
  success : B
  secretKey : List B
  publicKey : List B

def keygen (r : MlKemArithmetic.Ops W) (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (o : Word64.Ops B O) (k : Keccak.Ops B K)
    (rank eta pairs : Nat) (kyber : Bool) (seed : List B) : KeyPair B :=
  let hashed := Keccak.sha3_512 k (seed++(if kyber then [] else [a.const rank]))
  let rho := hashed.take 32
  let sigma := (hashed.drop 32).take 32
  let mat := matrix s a o k rank pairs false rho
  let secret := fun i => MlKemNtt.forward r s (noise r s a k eta sigma i)
  let error := fun i => MlKemNtt.forward r s (noise r s a k eta sigma (rank+i))
  let publicPolys := fun i => add r s (dot r s rank (mat.entries i) secret) (error i)
  ⟨mat.success,encode s a rank secret,encode s a rank publicPolys++rho⟩
structure Ciphertext (B : Type) where
  success : B
  bytes : List B

def encrypt (r : MlKemArithmetic.Ops W) (c : MlKemEncoding.Ops W) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (o : Word64.Ops B O) (k : Keccak.Ops B K) (rank eta du dv pairs : Nat)
    (publicKey message coins : List B) : Ciphertext B :=
  let t := decode s a rank publicKey
  let rho := (publicKey.drop (384*rank)).take 32
  let mat := matrix s a o k rank pairs true rho
  let ephemeral := fun i => MlKemNtt.forward r s (noise r s a k eta coins i)
  let error := fun i => noise r s a k 2 coins (rank+i)
  let error2 := noise r s a k 2 coins (2*rank)
  let msg := (MlKemEncoding.decode s a 1 256 message).map (MlKemEncoding.decompress r s 1)
  let u := fun i => add r s (MlKemNtt.inverse r s (dot r s rank (mat.entries i) ephemeral)) (error i)
  let v := add r s (add r s (MlKemNtt.inverse r s (dot r s rank t ephemeral)) error2) msg
  let packedU := (List.range rank).flatMap (fun i => MlKemEncoding.encode s a du 256 ((u i).map (MlKemEncoding.compress r c s du)))
  let packedV := MlKemEncoding.encode s a dv 256 (v.map (MlKemEncoding.compress r c s dv))
  ⟨mat.success,packedU++packedV⟩

def decrypt (r : MlKemArithmetic.Ops W) (c : MlKemEncoding.Ops W) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (rank du dv : Nat) (secretKey ciphertext : List B) : List B :=
  let secret := decode s a rank secretKey
  let u := fun i => (MlKemEncoding.decode s a du 256 ((ciphertext.drop (32*du*i)).take (32*du))).map (MlKemEncoding.decompress r s du)
  let v := (MlKemEncoding.decode s a dv 256 (ciphertext.drop (32*du*rank))).map (MlKemEncoding.decompress r s dv)
  let inner := MlKemNtt.inverse r s (dot r s rank secret (fun i => MlKemNtt.forward r s (u i)))
  MlKemEncoding.encode s a 1 256 ((sub r s v inner).map (MlKemEncoding.compress r c s 1))

inductive Operation where
  | keygen | encrypt | decrypt
  deriving BEq

def run (r : MlKemArithmetic.Ops W) (c : MlKemEncoding.Ops W) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (o : Word64.Ops B O) (k : Keccak.Ops B K) (rank eta du dv pairs : Nat) (kyber : Bool)
    (operation : Operation) (raw : List B) : List B :=
  let result : Ciphertext B := match operation with
    | .keygen =>
      let pair := keygen r s a o k rank eta pairs kyber raw
      ⟨pair.success,pair.secretKey++pair.publicKey⟩
    | .encrypt => encrypt r c s a o k rank eta du dv pairs (raw.take (384*rank+32)) ((raw.drop (384*rank+32)).take 32) (raw.drop (384*rank+64))
    | .decrypt => ⟨a.const 255,decrypt r c s a rank du dv (raw.take (384*rank)) (raw.drop (384*rank))⟩
  result.success :: result.bytes.map (a.and result.success)

def Matrix.map (f : B → B') (g : W → W') (m : Matrix B W) : Matrix B' W' :=
  ⟨f m.success,fun i j => (m.entries i j).map g⟩
def KeyPair.map (f : B → B') (m : KeyPair B) : KeyPair B' :=
  ⟨f m.success,m.secretKey.map f,m.publicKey.map f⟩
def Ciphertext.map (f : B → B') (m : Ciphertext B) : Ciphertext B' :=
  ⟨f m.success,m.bytes.map f⟩

section
variable {r : MlKemArithmetic.Ops W} {r' : MlKemArithmetic.Ops W'} {c : MlKemEncoding.Ops W} {c' : MlKemEncoding.Ops W'}
  {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {o : Word64.Ops B O} {o' : Word64.Ops B' O'} {k : Keccak.Ops B K} {k' : Keccak.Ops B' K'}
  {f : B → B'} {g : W → W'} {go : O → O'} {gk : K → K'}
  (hr : MlKemArithmetic.Hom r r' g) (hc : MlKemEncoding.Hom c c' g)
  (hs : Sha256.Hom s s' f g) (ha : ByteAuth.Hom a a' f)
  (ho : Word64.Hom o o' f go) (hk : Keccak.Hom k k' f gk)
include hs in
theorem zero_map : (zero s).map g = zero s' := by simp only [zero,List.map_replicate,hs.wordConst]
include hr hs in
theorem add_map (x y : Poly W) : (add r s x y).map g = add r' s' (x.map g) (y.map g) := by
  simp only [add,List.map_zipWith,List.zipWith_map_left,List.zipWith_map_right,MlKemArithmetic.addMod_map hr hs]
include hr hs in
theorem sub_map (x y : Poly W) : (sub r s x y).map g = sub r' s' (x.map g) (y.map g) := by
  simp only [sub,List.map_zipWith,List.zipWith_map_left,List.zipWith_map_right,MlKemArithmetic.subMod_map hr hs]
include hr hs in
theorem sumLoop_map (polys : List (Poly W)) (acc : Poly W) :
    (polys.foldl (add r s) acc).map g = (polys.map (List.map g)).foldl (add r' s') (acc.map g) := by
  induction polys generalizing acc with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons,List.map_cons,ih,add_map hr hs]
include hr hs in
theorem sum_map (polys : List (Poly W)) : (sum r s polys).map g = sum r' s' (polys.map (List.map g)) := by
  simp only [sum,sumLoop_map hr hs,zero_map hs]
include hr hs in
theorem dot_map (rank : Nat) (left right : Nat → Poly W) :
    (dot r s rank left right).map g = dot r' s' rank (fun i => (left i).map g) (fun i => (right i).map g) := by
  simp only [dot,sum_map hr hs,List.map_map,Function.comp_def,MlKemNtt.baseMultiply_map hr hs]
include hr hs ha hk in
theorem noise_map (eta : Nat) (seed : List B) (nonce : Nat) :
    (noise r s a k eta seed nonce).map g = noise r' s' a' k' eta (seed.map f) nonce := by
  simp only [noise,MlKemNtt.decodePoly_map hs ha,MlKemArithmetic.noise_map hr hs ha hk,List.map_append,List.map_cons,List.map_nil,ha.const]
include hs ha in
theorem decode_map (rank : Nat) (raw : List B) (i : Nat) :
    (decode s a rank raw i).map g = decode s' a' rank (raw.map f) i := by
  simp only [decode,MlKemEncoding.decode_map hs ha,List.map_take,List.map_drop]
include hs ha in
theorem encode_map (rank : Nat) (polys : Nat → Poly W) :
    (encode s a rank polys).map f = encode s' a' rank (fun i => (polys i).map g) := by
  simp only [encode,List.map_flatMap,MlKemEncoding.encode_map hs ha]
include ha in
theorem flags_map (rows : List (List B)) (flag : B) :
    f (rows.foldl (fun flag row => a.and flag (OpenResult.get a row 0)) flag) =
    (rows.map (List.map f)).foldl (fun flag row => a'.and flag (OpenResult.get a' row 0)) (f flag) := by
  induction rows generalizing flag with
  | nil => rfl
  | cons row rows ih => simp only [List.foldl_cons,List.map_cons,ih,ha.and,OpenResult.get_map ha]
include hs ha ho hk in
theorem matrix_map (rank pairs : Nat) (transpose : Bool) (rho : List B) :
    (matrix s a o k rank pairs transpose rho).map f g = matrix s' a' o' k' rank pairs transpose (rho.map f) := by
  have rowMap (i j : Nat) :
      (MlKemSample.matrix o a k 256 pairs (rho++(if transpose then [a.const i,a.const j] else [a.const j,a.const i]))).map f =
      MlKemSample.matrix o' a' k' 256 pairs (rho.map f++(if transpose then [a'.const i,a'.const j] else [a'.const j,a'.const i])) := by
    rw [MlKemSample.matrix_map ho ha hk]
    cases transpose <;> simp only [Bool.false_eq_true,↓reduceIte,List.map_append,List.map_cons,List.map_nil,ha.const]
  simp only [matrix,Matrix.map,flags_map ha,List.map_map,Function.comp_def,rowMap,ha.const]
  congr 1
  funext i j
  simp only [MlKemNtt.decodePoly_map hs ha,List.map_drop]
  have rows : (List.map (fun n => MlKemSample.matrix o' a' k' 256 pairs (rho.map f++(if transpose then [a'.const (n/rank),a'.const (n%rank)] else [a'.const (n%rank),a'.const (n/rank)]))) (List.range (rank*rank))) =
      ((List.range (rank*rank)).map (fun n => MlKemSample.matrix o a k 256 pairs (rho++(if transpose then [a.const (n/rank),a.const (n%rank)] else [a.const (n%rank),a.const (n/rank)])))).map (List.map f) := by
    simp only [List.map_map,Function.comp_def,rowMap]
  rw [rows]
  simp only [List.getElem?_map,Keccak.getD_map (List.map f),List.map_nil]
include hs ha ho hk in
theorem matrix_success_map (rank pairs : Nat) (transpose : Bool) (rho : List B) :
    f (matrix s a o k rank pairs transpose rho).success = (matrix s' a' o' k' rank pairs transpose (rho.map f)).success :=
  congrArg Matrix.success (matrix_map hs ha ho hk rank pairs transpose rho)
include hs ha ho hk in
theorem matrix_entry_map (rank pairs : Nat) (transpose : Bool) (rho : List B) (i j : Nat) :
    ((matrix s a o k rank pairs transpose rho).entries i j).map g =
      (matrix s' a' o' k' rank pairs transpose (rho.map f)).entries i j :=
  congrArg (fun m => m.entries i j) (matrix_map hs ha ho hk rank pairs transpose rho)
include hr hs ha ho hk in
theorem keygen_map (rank eta pairs : Nat) (kyber : Bool) (seed : List B) :
    (keygen r s a o k rank eta pairs kyber seed).map f = keygen r' s' a' o' k' rank eta pairs kyber (seed.map f) := by
  cases kyber <;> simp only [keygen,KeyPair.map,Bool.false_eq_true,↓reduceIte,
    matrix_success_map hs ha ho hk,encode_map hs ha,List.map_append,add_map hr hs,dot_map hr hs,
    MlKemNtt.forward_map hr hs,noise_map hr hs ha hk,matrix_entry_map hs ha ho hk,
    List.map_take,List.map_drop,Keccak.sha3_512,Keccak.hash_map hk,List.map_cons,List.map_nil,ha.const]
include hr hc hs ha ho hk in
theorem encrypt_map (rank eta du dv pairs : Nat) (publicKey message coins : List B) :
    (encrypt r c s a o k rank eta du dv pairs publicKey message coins).map f =
      encrypt r' c' s' a' o' k' rank eta du dv pairs (publicKey.map f) (message.map f) (coins.map f) := by
  simp only [encrypt,Ciphertext.map,matrix_success_map hs ha ho hk,List.map_append,List.map_flatMap,
    MlKemEncoding.encode_map hs ha,List.map_map,Function.comp_def,MlKemEncoding.compress_map hr hc hs]
  simp only [←List.map_map,←Function.comp_def]
  simp only [add_map hr hs,MlKemNtt.inverse_map hr hs,dot_map hr hs,MlKemNtt.forward_map hr hs,
    noise_map hr hs ha hk,matrix_entry_map hs ha ho hk,decode_map hs ha,List.map_take,List.map_drop,
    List.map_map,Function.comp_def,MlKemEncoding.decompress_map hr hs]
  rw [←MlKemEncoding.decode_map hs ha]
  simp only [List.map_map,Function.comp_def]
include hr hc hs ha in
theorem decrypt_map (rank du dv : Nat) (secretKey ciphertext : List B) :
    (decrypt r c s a rank du dv secretKey ciphertext).map f =
      decrypt r' c' s' a' rank du dv (secretKey.map f) (ciphertext.map f) := by
  simp only [decrypt,MlKemEncoding.encode_map hs ha]
  rw [List.map_map]
  simp only [Function.comp_def,MlKemEncoding.compress_map hr hc hs]
  simp only [←Function.comp_def,←List.map_map]
  simp only [sub_map hr hs,MlKemNtt.inverse_map hr hs,dot_map hr hs,decode_map hs ha,MlKemNtt.forward_map hr hs,
    List.map_map,Function.comp_def,MlKemEncoding.decompress_map hr hs]
  simp only [←List.map_map,←Function.comp_def,MlKemEncoding.decode_map hs ha,List.map_take,List.map_drop]
include hr hc hs ha ho hk in
theorem run_map (rank eta du dv pairs : Nat) (kyber : Bool) (operation : Operation) (raw : List B) :
    (run r c s a o k rank eta du dv pairs kyber operation raw).map f =
      run r' c' s' a' o' k' rank eta du dv pairs kyber operation (raw.map f) := by
  cases operation
  · simp only [run,←keygen_map hr hs ha ho hk,KeyPair.map,List.map_cons,List.map_map,List.map_append,Function.comp_def,ha.and]
  · simp only [run,←List.map_take,←List.map_drop,←encrypt_map hr hc hs ha ho hk,Ciphertext.map,List.map_cons,List.map_map,Function.comp_def,ha.and]
  · simp only [run,←List.map_take,←List.map_drop,←decrypt_map hr hc hs ha,List.map_cons,List.map_map,Function.comp_def,ha.and,ha.const]
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
end TlsMpc.Signal.MlKemPke
