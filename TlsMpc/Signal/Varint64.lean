import TlsMpc.Signal.Varint

/-! Ten-group canonical uint64 varints for secret SPQR epochs. Encoded width
is public; a shared mask checks it. The word and all emitted bytes are secret. -/
namespace TlsMpc.Signal.Varint64
open Std.Tactic.BVDecide

structure Ops (B W : Type) where
  pack : B → B → B → B → B → B → B → B → W
  group : W → Nat → B

def concrete : Ops (BitVec 8) (BitVec 64) where
  pack a b c d e f g h := ((a ++ b) ++ (c ++ d)) ++ ((e ++ f) ++ (g ++ h))
  group word i := word.extractLsb' (7 * i) 8 &&& 127

def symbolic : Ops (BVExpr 8) (BVExpr 64) where
  pack a b c d e f g h :=
    BvConstruct.append
      (BvConstruct.append (BvConstruct.append a b) (BvConstruct.append c d))
      (BvConstruct.append (BvConstruct.append e f) (BvConstruct.append g h))
  group word i := BvConstruct.bin (BvConstruct.extract (7 * i) 8 word) .and (.const 127)

structure Hom (o : Ops B W) (o' : Ops B' W') (f : B → B') (fw : W → W') : Prop where
  pack : ∀ a b c d e g h i, fw (o.pack a b c d e g h i) = o'.pack (f a) (f b) (f c) (f d) (f e) (f g) (f h) (f i)
  group : ∀ word i, f (o.group word i) = o'.group (fw word) i

def evaluationHom (assign : BVExpr.Assignment) :
    Hom symbolic concrete (BVExpr.eval assign) (BVExpr.eval assign) := by
  constructor <;> intros <;> simp [symbolic, concrete]

def pack (o : Ops B W) (a : ByteAuth.Ops B) (bytes : List B) : W :=
  o.pack (OpenResult.get a bytes 0) (OpenResult.get a bytes 1)
    (OpenResult.get a bytes 2) (OpenResult.get a bytes 3)
    (OpenResult.get a bytes 4) (OpenResult.get a bytes 5)
    (OpenResult.get a bytes 6) (OpenResult.get a bytes 7)

def groups (o : Ops B W) (word : W) : List B := (List.range 10).map (o.group word)

def widthMask (a : ByteAuth.Ops B) (payload : List B) (width : Nat) : B :=
  a.and (ByteAuth.equalMask a (payload.drop width) (List.replicate (10 - width) (a.const 0)))
    (if width = 1 then a.const 255 else a.not (ByteAuth.zeroMask a (OpenResult.get a payload (width - 1))))

def encode (o : Ops B W) (a : ByteAuth.Ops B) (word : W) (width : Nat) : List B :=
  Varint.encodeGroups a (groups o word) width

def accepts (o : Ops B W) (a : ByteAuth.Ops B) (word : W) (width : Nat) : B :=
  widthMask a (groups o word) width

def encodeCore (o : Ops B W) (a : ByteAuth.Ops B) (word : W) (width : Nat) : List B :=
  let accepted := accepts o a word width
  accepted :: ByteAuth.release a accepted (encode o a word width)

section Refinement
variable {o : Ops B W} {o' : Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {fw : W → W'} (ho : Hom o o' f fw) (ha : ByteAuth.Hom a a' f)
include ho

theorem groups_map (word : W) : (groups o word).map f = groups o' (fw word) := by
  simp only [groups, List.map_map, Function.comp_def, ho.group]

include ha
theorem pack_map (bytes : List B) : fw (pack o a bytes) = pack o' a' (bytes.map f) := by
  simp only [pack, ho.pack, OpenResult.get_map ha]

omit ho in
theorem widthMask_map (payload : List B) (width : Nat) :
    f (widthMask a payload width) = widthMask a' (payload.map f) width := by
  simp only [widthMask, ha.and, ByteAuth.equalMask_map ha, List.map_drop, List.map_replicate, ha.const]
  split <;> simp_all only [ha.const, ha.not, ByteAuth.zeroMask_map ha, OpenResult.get_map ha]

theorem encode_map (word : W) (width : Nat) :
    (encode o a word width).map f = encode o' a' (fw word) width := by
  simp only [encode, Varint.encodeGroups_map ha, groups_map ho]

theorem accepts_map (word : W) (width : Nat) :
    f (accepts o a word width) = accepts o' a' (fw word) width := by
  simp only [accepts, widthMask_map ha, groups_map ho]

theorem encodeCore_map (word : W) (width : Nat) :
    (encodeCore o a word width).map f = encodeCore o' a' (fw word) width := by
  simp only [encodeCore, List.map_cons, ByteAuth.release_map ha, accepts_map ho ha, encode_map ho ha]

end Refinement

theorem encode_length (o : Ops B W) (a : ByteAuth.Ops B) (word : W) (width : Nat) :
    (encode o a word width).length = width := by simp [encode, Varint.encodeGroups]

def canonicalGroups (payload : List (BitVec 8)) (width : Nat) : Prop :=
  payload.drop width = List.replicate (10 - width) 0 ∧
  (width = 1 ∨ OpenResult.get ByteAuth.concrete payload (width - 1) ≠ 0)

instance (payload : List (BitVec 8)) (width : Nat) : Decidable (canonicalGroups payload width) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem widthMask_value (payload : List (BitVec 8)) (width : Nat) :
    widthMask ByteAuth.concrete payload width = if canonicalGroups payload width then 255 else 0 := by
  have hc : ByteAuth.concrete.const 0 = (0 : BitVec 8) := rfl
  simp only [widthMask, hc, ByteAuth.equalMask_value, canonicalGroups]
  by_cases hw : width = 1
  · simp only [hw, if_true, true_or, and_true]
    split <;> rfl
  · simp only [if_neg hw, ByteAuth.zeroMask_value]
    by_cases hh : payload.drop width = List.replicate (10 - width) 0 <;>
      by_cases ht : OpenResult.get ByteAuth.concrete payload (width - 1) = 0 <;>
      simp only [hw, hh, ht, Ne, if_true, if_false, false_or, not_true_eq_false,
        not_false_eq_true, and_true, and_false] <;> rfl

theorem encodeCore_spec (word : BitVec 64) (width : Nat) :
    encodeCore concrete ByteAuth.concrete word width =
      if canonicalGroups (groups concrete word) width then
        255 :: encode concrete ByteAuth.concrete word width else 0 :: List.replicate width 0 := by
  simp only [encodeCore, accepts, widthMask_value]
  split
  · rw [ByteAuth.release_accept]
  · rw [ByteAuth.release_reject, encode_length]

theorem compiled_encode_correct (word : BVExpr 64) (width : Nat)
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (encode symbolic ByteAuth.symbolic word width).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (encode symbolic ByteAuth.symbolic word width))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (encode symbolic ByteAuth.symbolic word width))).vec.get index hi)) =
      (ByteCircuit.joinValue (encode concrete ByteAuth.concrete (word.eval assign) width)).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, encode_map (evaluationHom assign) (ByteAuth.evaluationHom assign)]

theorem compiled_encodeCore_correct (word : BVExpr 64) (width : Nat)
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (encodeCore symbolic ByteAuth.symbolic word width).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (encodeCore symbolic ByteAuth.symbolic word width))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (encodeCore symbolic ByteAuth.symbolic word width))).vec.get index hi)) =
      (ByteCircuit.joinValue (encodeCore concrete ByteAuth.concrete (word.eval assign) width)).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, encodeCore_map (evaluationHom assign) (ByteAuth.evaluationHom assign)]

end TlsMpc.Signal.Varint64
