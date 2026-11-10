import TlsMpc.ByteCircuit

/-! Shared exact reduction of a 64-byte little-endian integer modulo the
Edwards25519 subgroup order, matching Scalar::from_bytes_mod_order_wide.
SHA512 digest bytes are interpreted little-endian here, exactly as dalek does.
Uses the proved generic unsigned bit-vector remainder compiler. All inputs and
outputs remain shared. Actual dalek/Aeneas source refinement is not claimed. -/
namespace TlsMpc.Signal.XEdDsaScalar
open Std.Tactic.BVDecide
set_option maxRecDepth 4096
set_option exponentiation.threshold 1024

def order : Nat := 2^252+27742317777372353535851937790883648493
structure Ops (B W : Type) where
  zero : W
  push : W → B → W
  reduce : W → W
  byte : W → Nat → B

def concrete : Ops (BitVec 8) (BitVec 512) where
  zero := 0
  push x b := (x.extractLsb' 0 504) ++ b
  reduce x := x % BitVec.ofNat 512 order
  byte x i := x.extractLsb' (i*8) 8

def symbolic : Ops (BVExpr 8) (BVExpr 512) where
  zero := .const 0
  push x b := BvConstruct.append (BvConstruct.extract 0 504 x) b
  reduce x := BvConstruct.bin x .umod (.const (BitVec.ofNat 512 order))
  byte x i := BvConstruct.extract (i*8) 8 x

structure Hom (a : Ops B W) (b : Ops B' W') (f : B → B') (g : W → W') : Prop where
  zero : g a.zero = b.zero
  push : ∀ x v, g (a.push x v) = b.push (g x) (f v)
  reduce : ∀ x, g (a.reduce x) = b.reduce (g x)
  byte : ∀ x i, f (a.byte x i) = b.byte (g x) i

def evaluationHom (assign : BVExpr.Assignment) : Hom symbolic concrete (BVExpr.eval assign) (BVExpr.eval assign) := by
  constructor <;> intros <;> simp [symbolic,concrete]

def packLE (o : Ops B W) : List B → W
  | [] => o.zero
  | b :: bs => o.push (packLE o bs) b

def reduce (o : Ops B W) (bytes : List B) : List B :=
  let x := o.reduce (packLE o bytes)
  (List.range 32).map (o.byte x)

def decodeLE : List (BitVec 8) → Nat
  | [] => 0
  | b :: bs => b.toNat+256*decodeLE bs

theorem reduce_word_value (x : BitVec 512) : (concrete.reduce x).toNat = x.toNat % order := by
  simp only [concrete,BitVec.toNat_umod]
  rfl

theorem reduce_word_bound (x : BitVec 512) : (concrete.reduce x).toNat < order := by
  rw [reduce_word_value]
  exact Nat.mod_lt _ (by decide)

theorem decodeLE_bound (bytes : List (BitVec 8)) : decodeLE bytes < 256^bytes.length := by
  induction bytes with
  | nil => simp [decodeLE]
  | cons b bs ih =>
    have hb := b.isLt
    simp only [decodeLE,List.length_cons,Nat.pow_succ]
    omega

theorem packLE_value (bytes : List (BitVec 8)) (hlen : bytes.length ≤ 64) :
    (packLE concrete bytes).toNat = decodeLE bytes := by
  induction bytes with
  | nil => rfl
  | cons b bs ih =>
    have hbs : bs.length ≤ 63 := by simp only [List.length_cons] at hlen; omega
    have ih := ih (by omega)
    have bound := decodeLE_bound bs
    have powBound : 256^bs.length ≤ 256^63 := Nat.pow_le_pow_right (by decide) hbs
    have hfit : decodeLE bs < 2^504 := by omega
    change (((packLE concrete bs).extractLsb' 0 504) ++ b).toNat = b.toNat+256*decodeLE bs
    rw [BitVec.toNat_append,← Nat.shiftLeft_add_eq_or_of_lt b.isLt]
    simp only [BitVec.extractLsb'_toNat,Nat.shiftRight_zero,ih,Nat.mod_eq_of_lt hfit,Nat.shiftLeft_eq]
    omega

theorem reduce_input_value (bytes : List (BitVec 8)) (hlen : bytes.length = 64) :
    (concrete.reduce (packLE concrete bytes)).toNat = decodeLE bytes % order := by
  rw [reduce_word_value,packLE_value bytes (by omega)]

theorem reduce_bytes_spec (bytes : List (BitVec 8)) (hlen : bytes.length = 64) :
    (reduce concrete bytes).map BitVec.toNat =
      (List.range 32).map (fun i => (decodeLE bytes % order / 2^(i*8)) % 256) := by
  simp only [reduce,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro i _
  change ((concrete.reduce (packLE concrete bytes)).extractLsb' (i*8) 8).toNat = _
  rw [BitVec.extractLsb'_toNat,reduce_input_value bytes hlen,Nat.shiftRight_eq_div_pow]

section Refinement
variable {a : Ops B W} {b : Ops B' W'} {f : B → B'} {g : W → W'} (h : Hom a b f g)
include h

theorem packLE_map (bytes : List B) : g (packLE a bytes) = packLE b (bytes.map f) := by
  induction bytes with
  | nil => exact h.zero
  | cons x xs ih => simp only [packLE,List.map_cons,h.push,ih]
theorem reduce_map (bytes : List B) : (reduce a bytes).map f = reduce b (bytes.map f) := by
  simp only [reduce,List.map_map,Function.comp_def,h.byte,h.reduce,packLE_map h]
end Refinement

theorem reduce_length (o : Ops B W) (bytes : List B) : (reduce o bytes).length = 32 := by
  simp [reduce]

theorem compiled_reduce_correct (bytes : List (BVExpr 8)) (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8*(reduce symbolic bytes).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (reduce symbolic bytes))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (reduce symbolic bytes))).vec.get index hi)) =
      (ByteCircuit.joinValue (reduce concrete (bytes.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,reduce_map (evaluationHom assign)]
end TlsMpc.Signal.XEdDsaScalar
