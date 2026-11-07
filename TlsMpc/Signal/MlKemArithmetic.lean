import TlsMpc.Signal.Keccak
import TlsMpc.Signal.Varint

/-! Canonical modulo3329 arithmetic and centered-binomial sampling for the
ML-KEM/Kyber polynomial layer. Coefficients use shared32-bit words, serialized
as16-bit little-endian representatives0..3328. This deliberately simple Boolean
implementation uses proved generic unsigned remainder; optimized Montgomery
representations and actual libcrux arithmetic refinement remain separate. -/
namespace TlsMpc.Signal.MlKemArithmetic
open Std.Tactic.BVDecide

structure Ops (W : Type) where
  mul : W → W → W
  reduce : W → W

def concrete : Ops (BitVec 32) where
  mul := (· * ·)
  reduce x := x % (3329 : BitVec 32)
def symbolic : Ops (BVExpr 32) where
  mul x y := BvConstruct.bin x .mul y
  reduce x := BvConstruct.bin x .umod (.const 3329)
structure Hom (a : Ops W) (b : Ops W') (f : W → W') : Prop where
  mul : ∀ x y, f (a.mul x y) = b.mul (f x) (f y)
  reduce : ∀ x, f (a.reduce x) = b.reduce (f x)
def evaluationHom (assign : BVExpr.Assignment) : Hom symbolic concrete (BVExpr.eval assign) := by
  constructor <;> intros <;> simp [symbolic,concrete]

def sub (s : Sha256.Ops B W) (x y : W) : W := s.add x (s.add (s.not y) (s.wordConst 1))
def addMod (r : Ops W) (s : Sha256.Ops B W) (x y : W) : W := r.reduce (s.add x y)
def subMod (r : Ops W) (s : Sha256.Ops B W) (x y : W) : W := r.reduce (sub s (s.add (s.wordConst 3329) x) y)
def mulMod (r : Ops W) (x y : W) : W := r.reduce (r.mul x y)
def encode (s : Sha256.Ops B W) (x : W) : List B := [s.unpack x 3,s.unpack x 2]

def bit (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (input : List B) (index : Nat) : W :=
  s.pack (s.byteConst 0) (s.byteConst 0) (s.byteConst 0)
    (a.and (a.maskBit (OpenResult.get a input (index/8)) (index%8)) (a.const 1))
def bitSum (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (input : List B) (start : Nat) : Nat → W
  | 0 => s.wordConst 0
  | count+1 => s.add (bitSum s a input start count) (bit s a input (start+count))
def cbd (r : Ops W) (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (eta count : Nat) (input : List B) : List W :=
  (List.range count).map (fun i => subMod r s (bitSum s a input (2*eta*i) eta) (bitSum s a input (2*eta*i+eta) eta))
def cbdBytes (r : Ops W) (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (eta count : Nat) (input : List B) : List B :=
  (cbd r s a eta count input).flatMap (encode s)

def arithmeticBytes (r : Ops W) (s : Sha256.Ops B W) (x y : W) : List B :=
  encode s (addMod r s x y) ++ encode s (subMod r s x y) ++ encode s (mulMod r x y)
def noise (r : Ops W) (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (k : Keccak.Ops B K) (eta : Nat) (seedNonce : List B) : List B :=
  cbdBytes r s a eta 256 (Keccak.shake256 k (64*eta) seedNonce)

theorem sub_concrete (x y : BitVec 32) : sub Sha256.concrete x y = x-y := by
  simp only [sub,Sha256.concrete,BitVec.sub_eq_add_neg,BitVec.neg_eq_not_add]
theorem reduce_value (x : BitVec 32) : (concrete.reduce x).toNat = x.toNat % 3329 := by
  simp only [concrete,BitVec.toNat_umod]
  rfl
theorem reduce_bound (x : BitVec 32) : (concrete.reduce x).toNat < 3329 := by
  rw [reduce_value]
  exact Nat.mod_lt _ (by decide)
theorem addMod_value (x y : BitVec 32) (hx : x.toNat < 3329) (hy : y.toNat < 3329) :
    (addMod concrete Sha256.concrete x y).toNat = (x.toNat+y.toNat)%3329 := by
  unfold addMod
  rw [reduce_value]
  change (x+y).toNat % 3329 = _
  rw [BitVec.toNat_add_of_lt (by omega)]
theorem subMod_value (x y : BitVec 32) (hx : x.toNat < 3329) (hy : y.toNat < 3329) :
    (subMod concrete Sha256.concrete x y).toNat = (3329+x.toNat-y.toNat)%3329 := by
  unfold subMod
  rw [reduce_value,sub_concrete]
  change ((3329 : BitVec 32)+x-y).toNat % 3329 = _
  have hc : ((3329 : BitVec 32)+x).toNat = 3329+x.toNat := by
    rw [BitVec.toNat_add_of_lt (by change 3329+x.toNat < 2^32; omega)]
    rfl
  have hl : y ≤ (3329 : BitVec 32)+x := by
    change y.toNat ≤ ((3329 : BitVec 32)+x).toNat
    rw [hc]
    omega
  rw [BitVec.toNat_sub_of_le hl,hc]
theorem mulMod_value (x y : BitVec 32) (hx : x.toNat < 3329) (hy : y.toNat < 3329) :
    (mulMod concrete x y).toNat = (x.toNat*y.toNat)%3329 := by
  unfold mulMod
  rw [reduce_value]
  change (x*y).toNat % 3329 = _
  have hm := Nat.mul_le_mul (Nat.le_of_lt hx) (Nat.le_of_lt hy)
  rw [BitVec.toNat_mul_of_lt (by omega)]

theorem cbdBytes_length (r : Ops W) (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (eta count : Nat) (input : List B) :
    (cbdBytes r s a eta count input).length = 2*count := by
  simp only [cbdBytes,cbd,encode,List.length_flatMap,List.map_map,Function.comp_def,List.length_cons,List.length_nil]
  change (List.map (Function.const Nat 2) (List.range count)).sum = 2*count
  rw [List.map_const,List.length_range,List.sum_replicate_nat,Nat.mul_comm]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem oneBit_value (x : BitVec 8) (i : Fin 8) :
    (Sha256.concrete.pack 0 0 0 (ByteAuth.concrete.and (ByteAuth.concrete.maskBit x i.val) 1)).toNat =
      if x.getLsbD i.val then 1 else 0 := by
  have all : ∀ (x : BitVec 8) (i : Fin 8),
    (Sha256.concrete.pack 0 0 0 (ByteAuth.concrete.and (ByteAuth.concrete.maskBit x i.val) 1)).toNat =
      if x.getLsbD i.val then 1 else 0 := by decide +kernel
  exact all x i

def bitNat (input : List (BitVec 8)) (index : Nat) : Nat :=
  if (OpenResult.get ByteAuth.concrete input (index/8)).getLsbD (index%8) then 1 else 0
def sumNat (input : List (BitVec 8)) (start : Nat) : Nat → Nat
  | 0 => 0
  | count+1 => sumNat input start count + bitNat input (start+count)
theorem bit_value (input : List (BitVec 8)) (index : Nat) :
    (bit Sha256.concrete ByteAuth.concrete input index).toNat = bitNat input index :=
  oneBit_value _ ⟨index%8,Nat.mod_lt _ (by decide)⟩
theorem sumNat_bound (input : List (BitVec 8)) (start count : Nat) : sumNat input start count ≤ count := by
  induction count with
  | zero => exact Nat.le_refl 0
  | succ count ih =>
    simp only [sumNat,bitNat]
    split <;> omega
theorem bitSum_value (input : List (BitVec 8)) (start count : Nat) (hcount : count ≤ 3) :
    (bitSum Sha256.concrete ByteAuth.concrete input start count).toNat = sumNat input start count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have ih := ih (by omega)
    have hb := sumNat_bound input start count
    have hv := bit_value input (start+count)
    have hc : bitNat input (start+count) ≤ 1 := by unfold bitNat; split <;> omega
    simp only [bitSum,sumNat]
    change (_+_ : BitVec 32).toNat = _
    rw [BitVec.toNat_add_of_lt (by rw [ih,hv]; omega),ih,hv]

theorem cbd_values (eta count : Nat) (input : List (BitVec 8)) (heta : eta ≤ 3) :
    (cbd concrete Sha256.concrete ByteAuth.concrete eta count input).map BitVec.toNat =
      (List.range count).map (fun i => (3329+sumNat input (2*eta*i) eta-sumNat input (2*eta*i+eta) eta)%3329) := by
  simp only [cbd,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro i hi
  rw [subMod_value]
  · rw [bitSum_value _ _ _ heta,bitSum_value _ _ _ heta]
  · rw [bitSum_value _ _ _ heta]; have hb := sumNat_bound input (2*eta*i) eta; omega
  · rw [bitSum_value _ _ _ heta]; have hb := sumNat_bound input (2*eta*i+eta) eta; omega

section
variable {r : Ops W} {r' : Ops W'} {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {g : W → W'} (hr : Hom r r' g) (hs : Sha256.Hom s s' f g) (ha : ByteAuth.Hom a a' f)
include hs in
theorem sub_map (x y : W) : g (sub s x y) = sub s' (g x) (g y) := by simp only [sub,hs.add,hs.not,hs.wordConst]
include hr hs in
theorem addMod_map (x y : W) : g (addMod r s x y) = addMod r' s' (g x) (g y) := by simp only [addMod,hr.reduce,hs.add]
include hr hs in
theorem subMod_map (x y : W) : g (subMod r s x y) = subMod r' s' (g x) (g y) := by simp only [subMod,hr.reduce,sub_map hs,hs.add,hs.wordConst]
include hr in
theorem mulMod_map (x y : W) : g (mulMod r x y) = mulMod r' (g x) (g y) := by simp only [mulMod,hr.reduce,hr.mul]
include hs in
theorem encode_map (x : W) : (encode s x).map f = encode s' (g x) := by simp only [encode,List.map_cons,List.map_nil,hs.unpack]
include hs ha in
theorem bit_map (input : List B) (index : Nat) : g (bit s a input index) = bit s' a' (input.map f) index := by
  simp only [bit,hs.pack,hs.byteConst,ha.and,ha.maskBit,OpenResult.get_map ha,ha.const]
include hs ha in
theorem bitSum_map (input : List B) (start count : Nat) : g (bitSum s a input start count) = bitSum s' a' (input.map f) start count := by
  induction count with
  | zero => exact hs.wordConst 0
  | succ n ih => simp only [bitSum,hs.add,ih,bit_map hs ha]
include hr hs ha in
theorem cbd_map (eta count : Nat) (input : List B) : (cbd r s a eta count input).map g = cbd r' s' a' eta count (input.map f) := by
  simp only [cbd,List.map_map,Function.comp_def,subMod_map hr hs,bitSum_map hs ha]
include hr hs ha in
theorem cbdBytes_map (eta count : Nat) (input : List B) : (cbdBytes r s a eta count input).map f = cbdBytes r' s' a' eta count (input.map f) := by
  simp only [cbdBytes,List.map_flatMap,encode_map hs]
  rw [←List.flatMap_map, cbd_map hr hs ha]
include hr hs in
theorem arithmeticBytes_map (x y : W) :
    (arithmeticBytes r s x y).map f = arithmeticBytes r' s' (g x) (g y) := by
  simp only [arithmeticBytes,List.map_append,encode_map hs,addMod_map hr hs,subMod_map hr hs,mulMod_map hr]
include hr hs ha in
theorem noise_map {k : Keccak.Ops B K} {k' : Keccak.Ops B' K'} {gk : K → K'}
    (hk : Keccak.Hom k k' f gk) (eta : Nat) (seedNonce : List B) :
    (noise r s a k eta seedNonce).map f = noise r' s' a' k' eta (seedNonce.map f) := by
  simp only [noise,cbdBytes_map hr hs ha,Keccak.shake256,Keccak.hash_map hk]

end

theorem compiled_cbd_correct (eta count : Nat) (input : List (BVExpr 8)) (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8*(cbdBytes symbolic Sha256.symbolic ByteAuth.symbolic eta count input).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (cbdBytes symbolic Sha256.symbolic ByteAuth.symbolic eta count input))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (cbdBytes symbolic Sha256.symbolic ByteAuth.symbolic eta count input))).vec.get index hi)) =
      (ByteCircuit.joinValue (cbdBytes concrete Sha256.concrete ByteAuth.concrete eta count (input.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,cbdBytes_map (evaluationHom assign) (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]
theorem compiled_arithmetic_correct (x y : BVExpr 32) (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8*(arithmeticBytes symbolic Sha256.symbolic x y).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (arithmeticBytes symbolic Sha256.symbolic x y))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (arithmeticBytes symbolic Sha256.symbolic x y))).vec.get index hi)) =
      (ByteCircuit.joinValue (arithmeticBytes concrete Sha256.concrete (BVExpr.eval assign x) (BVExpr.eval assign y))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,arithmeticBytes_map (evaluationHom assign) (Sha256.evaluationHom assign)]

theorem compiled_noise_correct (eta : Nat) (input : List (BVExpr 8)) (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8*(noise symbolic Sha256.symbolic ByteAuth.symbolic Keccak.symbolic eta input).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (noise symbolic Sha256.symbolic ByteAuth.symbolic Keccak.symbolic eta input))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (noise symbolic Sha256.symbolic ByteAuth.symbolic Keccak.symbolic eta input))).vec.get index hi)) =
      (ByteCircuit.joinValue (noise concrete Sha256.concrete ByteAuth.concrete Keccak.concrete eta (input.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,noise_map (evaluationHom assign) (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign) (Keccak.evaluationHom assign)]

end TlsMpc.Signal.MlKemArithmetic
