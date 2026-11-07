import TlsMpc.Signal.SpqrDecodeAt
import TlsMpc.Signal.ReadAt
import TlsMpc.Signal.SpqrMessage

/-! Bounded SPQR V1 wire parser with entirely shared cursors. The only public
profile is the input length. Epoch/index varints, payload kind, chunk index and
data are selected in the circuit. Noncanonical varints and trailing bytes are
accepted as by the pinned SPQR parser. V0 negotiation is a separate operation.

Output: status || epochBE8 || indexBE4 || kind || hasChunk(0/1) ||
chunkIndexBE2 || chunkData32. Rejection zeros all 49 bytes. Ct1Ack is kind4
with no chunk, matching the receiver's `Ct1Ack(true)` interpretation. -/
namespace TlsMpc.Signal.SpqrParse
open Std.Tactic.BVDecide
open VarintDecode

def cursor (a : ByteAuth.Ops B) (result : List B) : List B :=
  OffsetSelect.normalize a 8 (result.drop 1)

def value (a : ByteAuth.Ops B) (result : List B) : List B :=
  OffsetSelect.normalize a 8 (result.drop 9)

structure Stages (B : Type) where
  epoch : List B
  index : List B
  kind : List B
  chunk : List B
  data : List B

def Stages.map (f : B → B') (stages : Stages B) : Stages B' :=
  ⟨stages.epoch.map f, stages.index.map f, stages.kind.map f,
    stages.chunk.map f, stages.data.map f⟩

def stages (o : Spqr.Ops B W) (a : ByteAuth.Ops B) (wire : List B) : Stages B :=
  let epoch := SpqrDecodeAt.decodeCore o a wire (OpenResult.encodeLength a 1)
  let index := SpqrDecodeAt.decodeCore o a wire (cursor a epoch)
  let kind := ReadAt.readCore a 1 wire (cursor a index)
  let chunk := SpqrDecodeAt.decodeCore o a wire (cursor a kind)
  let data := ReadAt.readCore a 32 wire (cursor a chunk)
  ⟨epoch, index, kind, chunk, data⟩

def statusMask (a : ByteAuth.Ops B) (result : List B) : B :=
  ByteAuth.eqMask a (OpenResult.get a result 0) (a.const 255)

def kindByte (a : ByteAuth.Ops B) (state : Stages B) : B := OpenResult.get a state.kind 9

def chunkMask (a : ByteAuth.Ops B) (state : Stages B) : B :=
  a.and (statusMask a state.chunk)
    (a.and (ByteAuth.equalMask a ((value a state.chunk).take 6) (List.replicate 6 (a.const 0)))
      (statusMask a state.data))

def payloadMask (a : ByteAuth.Ops B) (state : Stages B) : B :=
  let kind := kindByte a state
  a.xor (SpqrMessage.kindMask a false kind)
    (a.and (SpqrMessage.kindMask a true kind) (chunkMask a state))

def acceptedMask (a : ByteAuth.Ops B) (wire : List B) (state : Stages B) : B :=
  a.and (ByteAuth.eqMask a (OpenResult.get a wire 0) (a.const 1))
    (a.and (statusMask a state.epoch)
      (a.and (a.not (ByteAuth.equalMask a (value a state.epoch) (List.replicate 8 (a.const 0))))
        (a.and (statusMask a state.index)
          (a.and (ByteAuth.equalMask a ((value a state.index).take 4) (List.replicate 4 (a.const 0)))
            (a.and (statusMask a state.kind) (payloadMask a state))))))

def payload (a : ByteAuth.Ops B) (state : Stages B) : List B :=
  let hasChunk := SpqrMessage.kindMask a true (kindByte a state)
  value a state.epoch ++ (value a state.index).drop 4 ++
    [kindByte a state, a.and hasChunk (a.const 1)] ++
    ByteAuth.release a hasChunk ((value a state.chunk).drop 6 ++
      OffsetSelect.normalize a 32 (state.data.drop 9))

def finish (a : ByteAuth.Ops B) (wire : List B) (state : Stages B) : List B :=
  let accepted := acceptedMask a wire state
  accepted :: ByteAuth.release a accepted (payload a state)

def parseCore (o : Spqr.Ops B W) (a : ByteAuth.Ops B) (wire : List B) : List B :=
  finish a wire (stages o a wire)

def parseChecked (o : Spqr.Ops B W) (a : ByteAuth.Ops B) (wire : List B) : Option (List B) :=
  if wire.length ≤ 256 then some (parseCore o a wire) else none

theorem payload_length (a : ByteAuth.Ops B) (state : Stages B) :
    (payload a state).length = 48 := by
  simp [payload, value, OffsetSelect.normalize_length, ByteAuth.release]

theorem parseCore_length (o : Spqr.Ops B W) (a : ByteAuth.Ops B) (wire : List B) :
    (parseCore o a wire).length = 49 := by
  simp [parseCore, finish, ByteAuth.release, payload_length]

section Refinement
variable {o : Spqr.Ops B W} {o' : Spqr.Ops B' W'}
  {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} {fw : W → W'}
  (ho : Spqr.Hom o o' f fw) (ha : ByteAuth.Hom a a' f)
include ha

theorem cursor_map (result : List B) :
    (cursor a result).map f = cursor a' (result.map f) := by
  simp only [cursor, OffsetSelect.normalize_map ha, List.map_drop]

theorem value_map (result : List B) :
    (value a result).map f = value a' (result.map f) := by
  simp only [value, OffsetSelect.normalize_map ha, List.map_drop]

theorem statusMask_map (result : List B) :
    f (statusMask a result) = statusMask a' (result.map f) := by
  simp only [statusMask, ByteAuth.eqMask_map ha, OpenResult.get_map ha, ha.const]

theorem kindByte_map (state : Stages B) :
    f (kindByte a state) = kindByte a' (state.map f) := by
  simp only [kindByte, Stages.map, OpenResult.get_map ha]

theorem chunkMask_map (state : Stages B) :
    f (chunkMask a state) = chunkMask a' (state.map f) := by
  simp only [chunkMask, ha.and, statusMask_map ha, ByteAuth.equalMask_map ha,
    List.map_take, value_map ha, List.map_replicate, ha.const, Stages.map]

theorem payloadMask_map (state : Stages B) :
    f (payloadMask a state) = payloadMask a' (state.map f) := by
  simp only [payloadMask, ha.xor, ha.and, SpqrMessage.kindMask_map ha,
    kindByte_map ha, chunkMask_map ha]

theorem acceptedMask_map (wire : List B) (state : Stages B) :
    f (acceptedMask a wire state) = acceptedMask a' (wire.map f) (state.map f) := by
  simp only [acceptedMask, ha.and, ha.not, ByteAuth.eqMask_map ha, OpenResult.get_map ha,
    ha.const, statusMask_map ha, ByteAuth.equalMask_map ha, value_map ha,
    List.map_take, List.map_replicate, payloadMask_map ha, Stages.map]

theorem payload_map (state : Stages B) :
    (payload a state).map f = payload a' (state.map f) := by
  simp only [payload, List.map_append, List.map_drop, List.map_cons, List.map_nil,
    value_map ha, kindByte_map ha, ha.and, ha.const, SpqrMessage.kindMask_map ha,
    ByteAuth.release_map ha, OffsetSelect.normalize_map ha, Stages.map]

theorem finish_map (wire : List B) (state : Stages B) :
    (finish a wire state).map f = finish a' (wire.map f) (state.map f) := by
  simp only [finish, List.map_cons, ByteAuth.release_map ha, acceptedMask_map ha, payload_map ha]

include ho
theorem stages_map (wire : List B) :
    (stages o a wire).map f = stages o' a' (wire.map f) := by
  simp only [stages, Stages.map, SpqrDecodeAt.decodeCore_map ho ha,
    OpenResult.encodeLength_map ha, cursor_map ha, ReadAt.readCore_map ha]

theorem parseCore_map (wire : List B) :
    (parseCore o a wire).map f = parseCore o' a' (wire.map f) := by
  simp only [parseCore, finish_map ha, stages_map ho ha]

theorem parseChecked_map (wire : List B) :
    (parseChecked o a wire).map (List.map f) = parseChecked o' a' (wire.map f) := by
  simp only [parseChecked, List.length_map]
  split <;> simp [parseCore_map ho ha]
end Refinement

def chunkAccepted (state : Stages (BitVec 8)) : Prop :=
  OpenResult.get ByteAuth.concrete state.chunk 0 = 255 ∧
  (value ByteAuth.concrete state.chunk).take 6 = List.replicate 6 0 ∧
  OpenResult.get ByteAuth.concrete state.data 0 = 255

def payloadAccepted (state : Stages (BitVec 8)) : Prop :=
  SpqrMessage.validKind false (kindByte ByteAuth.concrete state) ∨
    (SpqrMessage.validKind true (kindByte ByteAuth.concrete state) ∧ chunkAccepted state)

def accepted (wire : List (BitVec 8)) (state : Stages (BitVec 8)) : Prop :=
  OpenResult.get ByteAuth.concrete wire 0 = 1 ∧
  OpenResult.get ByteAuth.concrete state.epoch 0 = 255 ∧
  value ByteAuth.concrete state.epoch ≠ List.replicate 8 0 ∧
  OpenResult.get ByteAuth.concrete state.index 0 = 255 ∧
  (value ByteAuth.concrete state.index).take 4 = List.replicate 4 0 ∧
  OpenResult.get ByteAuth.concrete state.kind 0 = 255 ∧ payloadAccepted state

instance (state : Stages (BitVec 8)) : Decidable (chunkAccepted state) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))
instance (state : Stages (BitVec 8)) : Decidable (payloadAccepted state) :=
  inferInstanceAs (Decidable (_ ∨ _))
instance (wire : List (BitVec 8)) (state : Stages (BitVec 8)) : Decidable (accepted wire state) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

theorem chunkMask_value (state : Stages (BitVec 8)) :
    chunkMask ByteAuth.concrete state = if chunkAccepted state then 255 else 0 := by
  have hc (n : Nat) : ByteAuth.concrete.const n = BitVec.ofNat 8 n := rfl
  simp only [chunkMask, statusMask, hc, ByteAuth.eqMask_value, ByteAuth.equalMask_value,
    Receive.mask_and, chunkAccepted]
  rfl

theorem payloadMask_value (state : Stages (BitVec 8)) :
    payloadMask ByteAuth.concrete state = if payloadAccepted state then 255 else 0 := by
  have disjoint : ¬ (SpqrMessage.validKind false (kindByte ByteAuth.concrete state) ∧
      SpqrMessage.validKind true (kindByte ByteAuth.concrete state)) := by
    simp only [SpqrMessage.validKind, Bool.false_eq_true, if_false, if_true]
    intro ⟨h, h'⟩
    rcases h with h | h <;> simp_all
  simp only [payloadMask, SpqrMessage.kindMask_value, chunkMask_value, Receive.mask_and,
    payloadAccepted]
  by_cases h : SpqrMessage.validKind false (kindByte ByteAuth.concrete state) <;>
    by_cases h' : SpqrMessage.validKind true (kindByte ByteAuth.concrete state) ∧ chunkAccepted state <;>
    simp_all [ByteAuth.concrete]

theorem acceptedMask_value (wire : List (BitVec 8)) (state : Stages (BitVec 8)) :
    acceptedMask ByteAuth.concrete wire state = if accepted wire state then 255 else 0 := by
  have neg (p : Prop) [Decidable p] :
      ByteAuth.concrete.not (if p then 255 else 0) = if ¬p then 255 else 0 := by
    by_cases h : p <;> simp [h, ByteAuth.concrete]
  have hc (n : Nat) : ByteAuth.concrete.const n = BitVec.ofNat 8 n := rfl
  simp only [acceptedMask, statusMask, hc, ByteAuth.eqMask_value, ByteAuth.equalMask_value,
    neg, payloadMask_value, Receive.mask_and, accepted]
  rfl

def spec (wire : List (BitVec 8)) : List (BitVec 8) :=
  let state := stages Spqr.concrete ByteAuth.concrete wire
  if accepted wire state then 255 :: payload ByteAuth.concrete state else List.replicate 49 0

theorem parseCore_spec (wire : List (BitVec 8)) :
    parseCore Spqr.concrete ByteAuth.concrete wire = spec wire := by
  simp only [parseCore, finish, acceptedMask_value, spec]
  split
  · rw [ByteAuth.release_accept]
  · rw [ByteAuth.release_reject, payload_length]; rfl

theorem compiled_parseCore_correct (wire : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (parseCore Spqr.symbolic ByteAuth.symbolic wire).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (parseCore Spqr.symbolic ByteAuth.symbolic wire))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (parseCore Spqr.symbolic ByteAuth.symbolic wire))).vec.get index hi)) =
      (ByteCircuit.joinValue (parseCore Spqr.concrete ByteAuth.concrete
        (wire.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,
    parseCore_map (Spqr.evaluationHom assign) (ByteAuth.evaluationHom assign)]

theorem compiled_parseCore_spec (wire : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (parseCore Spqr.symbolic ByteAuth.symbolic wire).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (parseCore Spqr.symbolic ByteAuth.symbolic wire))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (parseCore Spqr.symbolic ByteAuth.symbolic wire))).vec.get index hi)) =
      (ByteCircuit.joinValue (spec (wire.map (BVExpr.eval assign)))).getLsbD index := by
  rw [compiled_parseCore_correct, parseCore_spec]

end TlsMpc.Signal.SpqrParse
