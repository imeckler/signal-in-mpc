import TlsMpc.Signal.MlKemNtt

/-! Fixed-width little-endian ML-KEM polynomial encoding and rounded
compression. Public width and coefficient count determine circuit shape;
coefficients, packed bytes and decompression results stay shared. Raw 12-bit
unpacking is deliberately separate from public-key canonicality validation. -/
namespace TlsMpc.Signal.MlKemEncoding
open Std.Tactic.BVDecide
structure Ops (W : Type) where
  divQ : W → W
def concrete : Ops (BitVec 32) where
  divQ x := x / (3329 : BitVec 32)
def symbolic : Ops (BVExpr 32) where
  divQ x := BvConstruct.bin x .udiv (.const 3329)
structure Hom (a : Ops W) (b : Ops W') (f : W → W') : Prop where
  divQ : ∀ x, f (a.divQ x) = b.divQ (f x)
def evaluationHom (assign : BVExpr.Assignment) : Hom symbolic concrete (BVExpr.eval assign) := by
  constructor; intro x; simp [symbolic,concrete]

def compress (r : MlKemArithmetic.Ops W) (c : Ops W) (s : Sha256.Ops B W) (width : Nat) (x : W) : W :=
  s.and (c.divQ (s.add (r.mul x (s.wordConst (2^width))) (s.wordConst 1664))) (s.wordConst (2^width-1))
def decompress (r : MlKemArithmetic.Ops W) (s : Sha256.Ops B W) (width : Nat) (x : W) : W :=
  s.shr (s.add (r.mul x (s.wordConst 3329)) (s.wordConst (2^(width-1)))) width

def encodeByte (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (width : Nat) (poly : List W) (byteIndex : Nat) : B :=
  (List.range 8).foldl (fun acc bit =>
    let index := 8*byteIndex+bit
    let coeff := MlKemNtt.get s poly (index/width)
    a.xor acc (a.and (a.maskBit (s.unpack (s.shr coeff (index%width)) 3) 0) (a.const (2^bit)))) (a.const 0)
def encode (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (width count : Nat) (poly : List W) : List B :=
  (List.range ((width*count+7)/8)).map (encodeByte s a width poly)
def decodeCoeff (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (width : Nat) (input : List B) (index : Nat) : W :=
  (List.range width).foldl (fun acc bit => s.xor acc (s.rotr (MlKemArithmetic.bit s a input (width*index+bit)) (32-bit))) (s.wordConst 0)
def decode (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (width count : Nat) (input : List B) : List W :=
  (List.range count).map (decodeCoeff s a width input)

inductive Operation where
  | encode | decode | compress | decompress
  deriving BEq

def run (r : MlKemArithmetic.Ops W) (c : Ops W) (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (operation : Operation) (width : Nat) (raw : List B) : List B :=
  match operation with
  | .encode => encode s a width 256 (MlKemNtt.decodePoly s a raw)
  | .decode => MlKemNtt.encodePoly s (decode s a width 256 raw)
  | .compress => encode s a width 256 ((MlKemNtt.decodePoly s a raw).map (compress r c s width))
  | .decompress => MlKemNtt.encodePoly s ((decode s a width 256 raw).map (decompress r s width))

theorem encode_length (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (width count : Nat) (poly : List W) :
    (encode s a width count poly).length = (width*count+7)/8 := by simp [encode]
theorem decode_length (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (width count : Nat) (input : List B) :
    (decode s a width count input).length = count := by simp [decode]

theorem compress_value (width : Nat) (x : BitVec 32) (hw : width ≤ 12) (hx : x.toNat < 3329) :
    (compress MlKemArithmetic.concrete concrete Sha256.concrete width x).toNat =
      ((x.toNat*2^width+1664)/3329) % 2^width := by
  rw [←Nat.and_two_pow_sub_one_eq_mod]
  have hp : 2^width ≤ 4096 := Nat.pow_le_pow_right (by decide) hw
  have hp32 : 2^width < 2^32 := by omega
  have hm : x.toNat*2^width < 2^32 := by
    have := Nat.mul_le_mul (Nat.le_of_lt hx) hp
    omega
  have hmul : (x * BitVec.ofNat 32 (2^width)).toNat = x.toNat*2^width := by
    rw [BitVec.toNat_mul_of_lt]
    · simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hp32]
    · simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hp32] using hm
  change (((x * BitVec.ofNat 32 (2^width) + 1664) / 3329) &&& BitVec.ofNat 32 (2^width-1)).toNat = _
  rw [BitVec.toNat_and,BitVec.toNat_udiv,BitVec.toNat_add_of_lt]
  · rw [hmul]
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show 2^width-1 < 2^32 by omega)]
    rfl
  · rw [hmul]
    change x.toNat*2^width+1664 < 2^32
    have := Nat.mul_le_mul (Nat.le_of_lt hx) hp
    omega

set_option maxRecDepth 100000 in
theorem decompress_value (width : Nat) (x : BitVec 32) (hw : width ≤ 12) (hx : x.toNat < 2^width) :
    (decompress MlKemArithmetic.concrete Sha256.concrete width x).toNat =
      (x.toNat*3329+2^(width-1))/2^width := by
  have hp : 2^width ≤ 4096 := Nat.pow_le_pow_right (by decide) hw
  have hp' : 2^(width-1) ≤ 4096 := Nat.pow_le_pow_right (n := 2) (by decide) (show width-1 ≤ 12 by omega)
  have hm : x.toNat*3329 < 2^32 := by omega
  have hmul : (x * (3329 : BitVec 32)).toNat = x.toNat*3329 := by
    rw [BitVec.toNat_mul_of_lt (by simpa using hm)]
    rfl
  change ((x * 3329 + BitVec.ofNat 32 (2^(width-1))) >>> width).toNat = _
  rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,BitVec.toNat_add_of_lt]
  · rw [hmul]
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 2^(width-1) < 2^32 by omega)]
  · rw [hmul]
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 2^(width-1) < 2^32 by omega)]
    omega

section
variable {r : MlKemArithmetic.Ops W} {r' : MlKemArithmetic.Ops W'} {c : Ops W} {c' : Ops W'}
  {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {g : W → W'} (hr : MlKemArithmetic.Hom r r' g) (hc : Hom c c' g)
  (hs : Sha256.Hom s s' f g) (ha : ByteAuth.Hom a a' f)
include hr hc hs in
theorem compress_map (width : Nat) (x : W) : g (compress r c s width x) = compress r' c' s' width (g x) := by
  simp only [compress,hs.and,hc.divQ,hs.add,hr.mul,hs.wordConst]
include hr hs in
theorem decompress_map (width : Nat) (x : W) : g (decompress r s width x) = decompress r' s' width (g x) := by
  simp only [decompress,hs.shr,hs.add,hr.mul,hs.wordConst]
include hs ha in
theorem encodeLoop_map (bits : List Nat) (width : Nat) (poly : List W) (byteIndex : Nat) (acc : B) :
    f (bits.foldl (fun acc bit =>
      let index := 8*byteIndex+bit
      a.xor acc (a.and (a.maskBit (s.unpack (s.shr (MlKemNtt.get s poly (index/width)) (index%width)) 3) 0) (a.const (2^bit)))) acc) =
    bits.foldl (fun acc bit =>
      let index := 8*byteIndex+bit
      a'.xor acc (a'.and (a'.maskBit (s'.unpack (s'.shr (MlKemNtt.get s' (poly.map g) (index/width)) (index%width)) 3) 0) (a'.const (2^bit)))) (f acc) := by
  induction bits generalizing acc with
  | nil => rfl
  | cons bit bits ih => simp only [List.foldl_cons,ih,ha.xor,ha.and,ha.maskBit,hs.unpack,hs.shr,MlKemNtt.get_map hs,ha.const]
include hs ha in
theorem encodeByte_map (width : Nat) (poly : List W) (byteIndex : Nat) :
    f (encodeByte s a width poly byteIndex) = encodeByte s' a' width (poly.map g) byteIndex := by
  simp only [encodeByte,encodeLoop_map hs ha,ha.const]
include hs ha in
theorem encode_map (width count : Nat) (poly : List W) :
    (encode s a width count poly).map f = encode s' a' width count (poly.map g) := by
  simp only [encode,List.map_map,Function.comp_def,encodeByte_map hs ha]
include hs ha in
theorem decodeLoop_map (bits : List Nat) (width : Nat) (input : List B) (index : Nat) (acc : W) :
    g (bits.foldl (fun acc bit => s.xor acc (s.rotr (MlKemArithmetic.bit s a input (width*index+bit)) (32-bit))) acc) =
    bits.foldl (fun acc bit => s'.xor acc (s'.rotr (MlKemArithmetic.bit s' a' (input.map f) (width*index+bit)) (32-bit))) (g acc) := by
  induction bits generalizing acc with
  | nil => rfl
  | cons bit bits ih => simp only [List.foldl_cons,ih,hs.xor,hs.rotr,MlKemArithmetic.bit_map hs ha]
include hs ha in
theorem decodeCoeff_map (width : Nat) (input : List B) (index : Nat) :
    g (decodeCoeff s a width input index) = decodeCoeff s' a' width (input.map f) index := by
  simp only [decodeCoeff,decodeLoop_map hs ha,hs.wordConst]
include hs ha in
theorem decode_map (width count : Nat) (input : List B) :
    (decode s a width count input).map g = decode s' a' width count (input.map f) := by
  simp only [decode,List.map_map,Function.comp_def,decodeCoeff_map hs ha]
include hr hc hs ha in
theorem run_map (operation : Operation) (width : Nat) (raw : List B) :
    (run r c s a operation width raw).map f = run r' c' s' a' operation width (raw.map f) := by
  cases operation <;> simp only [run,encode_map hs ha,MlKemNtt.decodePoly_map hs ha,MlKemNtt.encodePoly_map hs,
    decode_map hs ha,List.map_map,Function.comp_def,compress_map hr hc hs,decompress_map hr hs]
  · rw [←MlKemNtt.decodePoly_map hs ha]; simp only [List.map_map,Function.comp_def]
  · rw [←decode_map hs ha]; simp only [List.map_map,Function.comp_def]
end

theorem compiled_run_correct (operation : Operation) (width : Nat) (raw : List (BVExpr 8)) (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8*(run MlKemArithmetic.symbolic symbolic Sha256.symbolic ByteAuth.symbolic operation width raw).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (run MlKemArithmetic.symbolic symbolic Sha256.symbolic ByteAuth.symbolic operation width raw))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (run MlKemArithmetic.symbolic symbolic Sha256.symbolic ByteAuth.symbolic operation width raw))).vec.get index hi)) =
      (ByteCircuit.joinValue (run MlKemArithmetic.concrete concrete Sha256.concrete ByteAuth.concrete operation width (raw.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,run_map (MlKemArithmetic.evaluationHom assign) (evaluationHom assign) (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]
end TlsMpc.Signal.MlKemEncoding
