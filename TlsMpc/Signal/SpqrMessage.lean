import TlsMpc.Signal.Varint64
import TlsMpc.Signal.ReceiveSpec

/-! Bounded SPQR V1 message serialization. Widths and chunk presence are public;
epoch, index, payload kind, chunk index and chunk data remain secret. The actual
serializer emits kind4 for either Ct1Ack Boolean, with no Boolean byte. -/
namespace TlsMpc.Signal.SpqrMessage
open Std.Tactic.BVDecide

structure Shape where
  epochWidth : Nat
  indexWidth : Nat
  chunkWidth : Nat
  hasChunk : Bool
  deriving DecidableEq

def Shape.valid (shape : Shape) : Prop :=
  1 ≤ shape.epochWidth ∧ shape.epochWidth ≤ 10 ∧
  1 ≤ shape.indexWidth ∧ shape.indexWidth ≤ 5 ∧
  (if shape.hasChunk then 1 ≤ shape.chunkWidth ∧ shape.chunkWidth ≤ 3 else shape.chunkWidth = 0)

instance (shape : Shape) : Decidable shape.valid := inferInstanceAs (Decidable (_ ∧ _))

def chunkWord (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (bytes : List B) : W :=
  s.pack (a.const 0) (a.const 0) (OpenResult.get a bytes 0) (OpenResult.get a bytes 1)

def kindMask (a : ByteAuth.Ops B) (hasChunk : Bool) (kind : B) : B :=
  if hasChunk then
    a.xor (ByteAuth.eqMask a kind (a.const 1))
      (a.xor (ByteAuth.eqMask a kind (a.const 2))
        (a.xor (ByteAuth.eqMask a kind (a.const 3))
          (a.xor (ByteAuth.eqMask a kind (a.const 5)) (ByteAuth.eqMask a kind (a.const 6)))))
  else a.xor (ByteAuth.eqMask a kind (a.const 0)) (ByteAuth.eqMask a kind (a.const 4))

def content (v : Varint64.Ops B V) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (shape : Shape) (epoch : V) (index : W) (kind : B) (chunkIndex chunkData : List B) : List B :=
  [a.const 1] ++ Varint64.encode v a epoch shape.epochWidth ++
    Varint.encode s a index shape.indexWidth ++ [kind] ++
    (if shape.hasChunk then Varint.encode s a (chunkWord s a chunkIndex) shape.chunkWidth ++ chunkData else [])

def acceptedMask (v : Varint64.Ops B V) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (shape : Shape) (epoch : V) (index : W) (kind : B) (chunkIndex : List B) : B :=
  a.and (Varint64.accepts v a epoch shape.epochWidth)
    (a.and (Varint.accepts s a index shape.indexWidth)
      (a.and (kindMask a shape.hasChunk kind)
        (if shape.hasChunk then Varint.accepts s a (chunkWord s a chunkIndex) shape.chunkWidth else a.const 255)))

def encodeCore (v : Varint64.Ops B V) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (shape : Shape) (epoch : V) (index : W) (kind : B) (chunkIndex chunkData : List B) : List B :=
  let accepted := acceptedMask v s a shape epoch index kind chunkIndex
  accepted :: ByteAuth.release a accepted (content v s a shape epoch index kind chunkIndex chunkData)

def inputShape (shape : Shape) (epoch index chunkIndex chunkData : List B) : Prop :=
  shape.valid ∧ epoch.length = 8 ∧ index.length = 4 ∧
  chunkIndex.length = (if shape.hasChunk then 2 else 0) ∧
  chunkData.length = (if shape.hasChunk then 32 else 0)

instance (shape : Shape) (epoch index chunkIndex chunkData : List B) :
    Decidable (inputShape shape epoch index chunkIndex chunkData) := inferInstanceAs (Decidable (_ ∧ _))

def encodeChecked (v : Varint64.Ops B V) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (shape : Shape) (epoch index : List B) (kind : B) (chunkIndex chunkData : List B) : Option (List B) :=
  if inputShape shape epoch index chunkIndex chunkData then
    some (encodeCore v s a shape (Varint64.pack v a epoch) (Varint.pack s a index) kind chunkIndex chunkData)
  else none

section Refinement
variable {v : Varint64.Ops B V} {v' : Varint64.Ops B' V'}
  {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'}
  {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} {fw : W → W'} {fv : V → V'}
  (hv : Varint64.Hom v v' f fv) (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)
include hs ha

theorem chunkWord_map (bytes : List B) : fw (chunkWord s a bytes) = chunkWord s' a' (bytes.map f) := by
  simp only [chunkWord, hs.pack, ha.const, OpenResult.get_map ha]

omit hs in
theorem kindMask_map (hasChunk : Bool) (kind : B) :
    f (kindMask a hasChunk kind) = kindMask a' hasChunk (f kind) := by
  simp only [kindMask]
  split <;> simp only [ha.xor, ByteAuth.eqMask_map ha, ha.const]

include hv
theorem content_map (shape : Shape) (epoch : V) (index : W) (kind : B) (chunkIndex chunkData : List B) :
    (content v s a shape epoch index kind chunkIndex chunkData).map f =
      content v' s' a' shape (fv epoch) (fw index) (f kind) (chunkIndex.map f) (chunkData.map f) := by
  simp only [content, List.map_append, List.map_cons, List.map_nil, ha.const,
    Varint64.encode_map hv ha, Varint.encode_map hs ha]
  split <;> simp only [List.map_append, List.map_nil, Varint.encode_map hs ha, chunkWord_map hs ha]

theorem acceptedMask_map (shape : Shape) (epoch : V) (index : W) (kind : B) (chunkIndex : List B) :
    f (acceptedMask v s a shape epoch index kind chunkIndex) =
      acceptedMask v' s' a' shape (fv epoch) (fw index) (f kind) (chunkIndex.map f) := by
  simp only [acceptedMask, ha.and, Varint64.accepts_map hv ha,
    Varint.accepts_map hs ha, kindMask_map ha]
  split <;> simp only [ha.const, Varint.accepts_map hs ha, chunkWord_map hs ha]

theorem encodeCore_map (shape : Shape) (epoch : V) (index : W) (kind : B) (chunkIndex chunkData : List B) :
    (encodeCore v s a shape epoch index kind chunkIndex chunkData).map f =
      encodeCore v' s' a' shape (fv epoch) (fw index) (f kind) (chunkIndex.map f) (chunkData.map f) := by
  simp only [encodeCore, List.map_cons, ByteAuth.release_map ha,
    acceptedMask_map hv hs ha, content_map hv hs ha]

theorem encodeChecked_map (shape : Shape) (epoch index : List B) (kind : B) (chunkIndex chunkData : List B) :
    (encodeChecked v s a shape epoch index kind chunkIndex chunkData).map (List.map f) =
      encodeChecked v' s' a' shape (epoch.map f) (index.map f) (f kind) (chunkIndex.map f) (chunkData.map f) := by
  simp only [encodeChecked, inputShape, List.length_map]
  split <;> simp [encodeCore_map hv hs ha, Varint64.pack_map hv ha, Varint.pack_map hs ha]

end Refinement

def validKind (hasChunk : Bool) (kind : BitVec 8) : Prop :=
  if hasChunk then kind = 1 ∨ kind = 2 ∨ kind = 3 ∨ kind = 5 ∨ kind = 6 else kind = 0 ∨ kind = 4

instance (hasChunk : Bool) (kind : BitVec 8) : Decidable (validKind hasChunk kind) :=
  by unfold validKind; split <;> infer_instance

theorem kindMask_value (hasChunk : Bool) (kind : BitVec 8) :
    kindMask ByteAuth.concrete hasChunk kind = if validKind hasChunk kind then 255 else 0 := by
  have all : ∀ (hasChunk : Bool) (kind : BitVec 8),
      kindMask ByteAuth.concrete hasChunk kind = if validKind hasChunk kind then 255 else 0 := by
    decide +kernel
  exact all hasChunk kind

def accepted (shape : Shape) (epoch : BitVec 64) (index : BitVec 32) (kind : BitVec 8)
    (chunkIndex : List (BitVec 8)) : Prop :=
  Varint64.canonicalGroups (Varint64.groups Varint64.concrete epoch) shape.epochWidth ∧
  Varint.canonicalGroups (Varint.groups Sha256.concrete ByteAuth.concrete index) shape.indexWidth ∧
  validKind shape.hasChunk kind ∧
  (if shape.hasChunk then Varint.canonicalGroups
    (Varint.groups Sha256.concrete ByteAuth.concrete (chunkWord Sha256.concrete ByteAuth.concrete chunkIndex))
      shape.chunkWidth else True)

instance (shape : Shape) (epoch : BitVec 64) (index : BitVec 32) (kind : BitVec 8)
    (chunkIndex : List (BitVec 8)) : Decidable (accepted shape epoch index kind chunkIndex) :=
  by unfold accepted; infer_instance

theorem acceptedMask_value (shape : Shape) (epoch : BitVec 64) (index : BitVec 32) (kind : BitVec 8)
    (chunkIndex : List (BitVec 8)) :
    acceptedMask Varint64.concrete Sha256.concrete ByteAuth.concrete shape epoch index kind chunkIndex =
      if accepted shape epoch index kind chunkIndex then 255 else 0 := by
  have hconst : ByteAuth.concrete.const 255 = (255 : BitVec 8) := rfl
  have hand (x : BitVec 8) : ByteAuth.concrete.and x 255 = x := BitVec.and_allOnes
  cases hb : shape.hasChunk <;>
    simp only [acceptedMask, Varint64.accepts, Varint.accepts, Varint64.widthMask_value,
      Varint.widthMask_value, kindMask_value, hb, Bool.false_eq_true, if_false, if_true,
      hconst, hand, Receive.mask_and, accepted, hb, and_true]

theorem encodeCore_spec (shape : Shape) (epoch : BitVec 64) (index : BitVec 32) (kind : BitVec 8)
    (chunkIndex chunkData : List (BitVec 8)) :
    encodeCore Varint64.concrete Sha256.concrete ByteAuth.concrete shape epoch index kind chunkIndex chunkData =
      if accepted shape epoch index kind chunkIndex then
        255 :: content Varint64.concrete Sha256.concrete ByteAuth.concrete shape epoch index kind chunkIndex chunkData
      else 0 :: List.replicate
        (content Varint64.concrete Sha256.concrete ByteAuth.concrete shape epoch index kind chunkIndex chunkData).length 0 := by
  simp only [encodeCore, acceptedMask_value]
  split
  · rw [ByteAuth.release_accept]
  · rw [ByteAuth.release_reject]

theorem content_length (v : Varint64.Ops B V) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (shape : Shape) (epoch : V) (index : W) (kind : B) (chunkIndex chunkData : List B) :
    (content v s a shape epoch index kind chunkIndex chunkData).length =
      2 + shape.epochWidth + shape.indexWidth +
        (if shape.hasChunk then shape.chunkWidth + chunkData.length else 0) := by
  simp only [content, List.length_append, List.length_cons, List.length_nil,
    Varint64.encode_length, Varint.encode_length]
  split <;> simp [Varint.encode_length] <;> omega

theorem compiled_content_correct (shape : Shape) (epoch : BVExpr 64) (index : BVExpr 32) (kind : BVExpr 8)
    (chunkIndex chunkData : List (BVExpr 8)) (assign : BVExpr.Assignment) (bit : Nat)
    (hi : bit < 8 * (content Varint64.symbolic Sha256.symbolic ByteAuth.symbolic shape epoch index kind chunkIndex chunkData).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (content Varint64.symbolic Sha256.symbolic ByteAuth.symbolic shape epoch index kind chunkIndex chunkData))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (content Varint64.symbolic Sha256.symbolic ByteAuth.symbolic shape epoch index kind chunkIndex chunkData))).vec.get bit hi)) =
      (ByteCircuit.joinValue (content Varint64.concrete Sha256.concrete ByteAuth.concrete shape
        (epoch.eval assign) (index.eval assign) (kind.eval assign)
        (chunkIndex.map (BVExpr.eval assign)) (chunkData.map (BVExpr.eval assign)))).getLsbD bit := by
  rw [ByteCircuit.compile_bytes_correct, content_map (Varint64.evaluationHom assign)
    (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]

theorem compiled_encodeCore_correct (shape : Shape) (epoch : BVExpr 64) (index : BVExpr 32) (kind : BVExpr 8)
    (chunkIndex chunkData : List (BVExpr 8)) (assign : BVExpr.Assignment) (bit : Nat)
    (hi : bit < 8 * (encodeCore Varint64.symbolic Sha256.symbolic ByteAuth.symbolic shape epoch index kind chunkIndex chunkData).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (encodeCore Varint64.symbolic Sha256.symbolic ByteAuth.symbolic shape epoch index kind chunkIndex chunkData))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (encodeCore Varint64.symbolic Sha256.symbolic ByteAuth.symbolic shape epoch index kind chunkIndex chunkData))).vec.get bit hi)) =
      (ByteCircuit.joinValue (encodeCore Varint64.concrete Sha256.concrete ByteAuth.concrete shape
        (epoch.eval assign) (index.eval assign) (kind.eval assign)
        (chunkIndex.map (BVExpr.eval assign)) (chunkData.map (BVExpr.eval assign)))).getLsbD bit := by
  rw [ByteCircuit.compile_bytes_correct, encodeCore_map (Varint64.evaluationHom assign)
    (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]

end TlsMpc.Signal.SpqrMessage
