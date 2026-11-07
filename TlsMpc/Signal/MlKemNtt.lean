import TlsMpc.Signal.MlKemArithmetic

/-! Canonical-coefficient ML-KEM/Kyber NTT, inverse NTT and quadratic base
multiplication. Every polynomial has256 coefficients in serialized profiles.
Public indices and roots of unity are computed before MPC; coefficients remain
shared. The compiler theorem is separate from actual libcrux refinement and
from an algebraic security argument. -/
namespace TlsMpc.Signal.MlKemNtt
open Std.Tactic.BVDecide MlKemArithmetic

def reverseBits : Nat → Nat → Nat
  | 0, _ => 0
  | width+1, x => (x%2)*2^width+reverseBits width (x/2)
def zeta (i : Nat) : Nat := 17^(reverseBits 7 i)%3329

def get (s : Sha256.Ops B W) (poly : List W) (i : Nat) : W := poly[i]?.getD (s.wordConst 0)
def forwardLayer (r : Ops W) (s : Sha256.Ops B W) (level : Nat) (poly : List W) : List W :=
  let length := 128/2^level
  (List.range 256).map (fun i =>
    let position := i%(2*length)
    let group := i/(2*length)
    let root := s.wordConst (zeta (2^level+group))
    if position < length then addMod r s (get s poly i) (mulMod r root (get s poly (i+length)))
    else subMod r s (get s poly (i-length)) (mulMod r root (get s poly i)))
def inverseLayer (r : Ops W) (s : Sha256.Ops B W) (level : Nat) (poly : List W) : List W :=
  let length := 2*2^level
  (List.range 256).map (fun i =>
    let position := i%(2*length)
    let group := i/(2*length)
    let root := s.wordConst (zeta (128/2^level-1-group))
    if position < length then addMod r s (get s poly i) (get s poly (i+length))
    else mulMod r root (subMod r s (get s poly i) (get s poly (i-length))))
def forward (r : Ops W) (s : Sha256.Ops B W) (poly : List W) : List W :=
  (List.range 7).foldl (fun state level => forwardLayer r s level state) poly
def inverse (r : Ops W) (s : Sha256.Ops B W) (poly : List W) : List W :=
  let transformed := (List.range 7).foldl (fun state level => inverseLayer r s level state) poly
  transformed.map (fun x => mulMod r x (s.wordConst 3303))
def baseMultiply (r : Ops W) (s : Sha256.Ops B W) (left right : List W) : List W :=
  (List.range 256).map (fun i =>
    let pair := i/2
    let a0 := get s left (2*pair)
    let a1 := get s left (2*pair+1)
    let b0 := get s right (2*pair)
    let b1 := get s right (2*pair+1)
    if i%2 = 0 then addMod r s (mulMod r a0 b0)
      (mulMod r (s.wordConst (17^(2*reverseBits 7 pair+1)%3329)) (mulMod r a1 b1))
    else addMod r s (mulMod r a0 b1) (mulMod r a1 b0))

def encodePoly (s : Sha256.Ops B W) (poly : List W) : List B := poly.flatMap (MlKemArithmetic.encode s)
def decodePoly (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (raw : List B) : List W :=
  (List.range 256).map (fun i => s.pack (s.byteConst 0) (s.byteConst 0) (OpenResult.get a raw (2*i+1)) (OpenResult.get a raw (2*i)))

inductive Operation where
  | forward | inverse | multiply
  deriving BEq

def run (r : Ops W) (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (operation : Operation) (raw : List B) : List B :=
  let left := decodePoly s a (raw.take 512)
  encodePoly s (match operation with
    | .forward => forward r s left
    | .inverse => inverse r s left
    | .multiply => baseMultiply r s left (decodePoly s a (raw.drop 512)))

section
variable {r : Ops W} {r' : Ops W'} {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {g : W → W'} (hr : MlKemArithmetic.Hom r r' g) (hs : Sha256.Hom s s' f g) (ha : ByteAuth.Hom a a' f)
include hs in
theorem get_map (poly : List W) (i : Nat) : g (get s poly i) = get s' (poly.map g) i := by
  simp only [get,List.getElem?_map,Keccak.getD_map g,hs.wordConst]
include hr hs in
theorem forwardLayer_map (level : Nat) (poly : List W) :
    (forwardLayer r s level poly).map g = forwardLayer r' s' level (poly.map g) := by
  simp only [forwardLayer,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro i hi
  split <;> simp only [addMod_map hr hs,subMod_map hr hs,mulMod_map hr,hs.wordConst,get_map hs]
include hr hs in
theorem inverseLayer_map (level : Nat) (poly : List W) :
    (inverseLayer r s level poly).map g = inverseLayer r' s' level (poly.map g) := by
  simp only [inverseLayer,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro i hi
  split <;> simp only [addMod_map hr hs,subMod_map hr hs,mulMod_map hr,hs.wordConst,get_map hs]
include hr hs in
theorem forwardLoop_map (levels : List Nat) (poly : List W) :
    (levels.foldl (fun state level => forwardLayer r s level state) poly).map g =
      levels.foldl (fun state level => forwardLayer r' s' level state) (poly.map g) := by
  induction levels generalizing poly with
  | nil => rfl
  | cons level levels ih => simp only [List.foldl_cons,ih,forwardLayer_map hr hs]
include hr hs in
theorem inverseLoop_map (levels : List Nat) (poly : List W) :
    (levels.foldl (fun state level => inverseLayer r s level state) poly).map g =
      levels.foldl (fun state level => inverseLayer r' s' level state) (poly.map g) := by
  induction levels generalizing poly with
  | nil => rfl
  | cons level levels ih => simp only [List.foldl_cons,ih,inverseLayer_map hr hs]
include hr hs in
theorem forward_map (poly : List W) : (forward r s poly).map g = forward r' s' (poly.map g) := forwardLoop_map hr hs _ _
include hr hs in
theorem inverse_map (poly : List W) : (inverse r s poly).map g = inverse r' s' (poly.map g) := by
  simp only [inverse,List.map_map,Function.comp_def,mulMod_map hr,hs.wordConst]
  rw [←inverseLoop_map hr hs]
  simp only [List.map_map,Function.comp_def]
include hr hs in
theorem baseMultiply_map (left right : List W) :
    (baseMultiply r s left right).map g = baseMultiply r' s' (left.map g) (right.map g) := by
  simp only [baseMultiply,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro i hi
  split <;> simp only [addMod_map hr hs,mulMod_map hr,hs.wordConst,get_map hs]
include hs in
theorem encodePoly_map (poly : List W) : (encodePoly s poly).map f = encodePoly s' (poly.map g) := by
  simp only [encodePoly,List.map_flatMap,List.flatMap_map,Function.comp_def,encode_map hs]
include hs ha in
theorem decodePoly_map (raw : List B) : (decodePoly s a raw).map g = decodePoly s' a' (raw.map f) := by
  simp only [decodePoly,List.map_map,Function.comp_def,hs.pack,hs.byteConst,OpenResult.get_map ha]
include hr hs ha in
theorem run_map (operation : Operation) (raw : List B) : (run r s a operation raw).map f = run r' s' a' operation (raw.map f) := by
  cases operation <;> simp only [run,encodePoly_map hs,forward_map hr hs,inverse_map hr hs,baseMultiply_map hr hs,
    decodePoly_map hs ha,List.map_take,List.map_drop]
end

theorem compiled_run_correct (operation : Operation) (raw : List (BVExpr 8)) (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8*(run MlKemArithmetic.symbolic Sha256.symbolic ByteAuth.symbolic operation raw).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (run MlKemArithmetic.symbolic Sha256.symbolic ByteAuth.symbolic operation raw))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (run MlKemArithmetic.symbolic Sha256.symbolic ByteAuth.symbolic operation raw))).vec.get index hi)) =
      (ByteCircuit.joinValue (run MlKemArithmetic.concrete Sha256.concrete ByteAuth.concrete operation (raw.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,run_map (MlKemArithmetic.evaluationHom assign) (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]
end TlsMpc.Signal.MlKemNtt
