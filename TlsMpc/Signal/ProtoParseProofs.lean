import TlsMpc.Signal.ProtoParse

namespace TlsMpc.Signal.ProtoParse
open Std.Tactic.BVDecide

section Refinement
variable {d : VarintDecode.Spqr.Ops B W} {d' : VarintDecode.Spqr.Ops B' W'}
  {o : Word64.Ops B W} {o' : Word64.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {fw : W → W'}
  (hd : VarintDecode.Spqr.Hom d d' f fw) (ho : Word64.Hom o o' f fw) (ha : ByteAuth.Hom a a' f)

include hd ho ha in
theorem decodePrefix_map (wire : List B) (start : Nat) :
    (decodePrefix d o a wire start).map f fw = decodePrefix d' o' a' (wire.map f) start := by
  simp only [decodePrefix, Decoded.map, ha.and, Word64.bor_map ha, ha.not,
    ByteAuth.eqMask_map ha, ByteAuth.zeroMask_map ha, OpenResult.get_map ha, ha.const,
    ho.add, ho.const, ho.pack, List.map_append, List.map_replicate, List.map_cons, List.map_nil,
    List.map_drop, VarintDecode.Spqr.decodeCore_map hd ha]

include ho ha in
theorem selectDecoded_map (mask : B) (yes no : Decoded B W) :
    (selectDecoded o a mask yes no).map f fw = selectDecoded o' a' (f mask) (yes.map f fw) (no.map f fw) := by
  simp [selectDecoded, Decoded.map, Unpad.chooseByte_map ha, ho.select]

include ho ha in
theorem lookupDecoded_map (index : W) (start : Nat) (rows : List (Decoded B W)) :
    (lookupDecoded o a index start rows).map f fw =
      lookupDecoded o' a' (fw index) start (rows.map (Decoded.map f fw)) := by
  induction rows generalizing start with
  | nil => simp [lookupDecoded, Decoded.map, ha.const, ho.const]
  | cons row rest ih =>
      simp only [lookupDecoded, List.map_cons, selectDecoded_map ho ha,
        Word64.eq_map ho ha, ho.const, ih]

include hd ho ha in
theorem table_map (wire : List B) :
    (table d o a wire).map (Decoded.map f fw) = table d' o' a' (wire.map f) := by
  simp only [table, List.map_map, Function.comp_def, List.length_map, decodePrefix_map hd ho ha]

include ho ha in
theorem emptyField_map : (emptyField o a).map f fw = emptyField o' a' := by
  simp [emptyField, Field.map, ha.const, ho.const]

include ho ha in
theorem selectField_map (mask : B) (yes no : Field B W) :
    (selectField o a mask yes no).map f fw = selectField o' a' (f mask) (yes.map f fw) (no.map f fw) := by
  simp [selectField, Field.map, Unpad.chooseByte_map ha, ho.select]

include ho ha in
theorem initial_map (capacity : Nat) : (initial o a capacity).map f fw = initial o' a' capacity := by
  simp [initial, State.map, ha.const, ho.const, emptyField_map ho ha]

include ho ha in
theorem lookupWord_map (index : W) (start : Nat) (rows : List W) :
    fw (lookupWord o a index start rows) = lookupWord o' a' (fw index) start (rows.map fw) := by
  induction rows generalizing start with
  | nil => simp [lookupWord, ho.const]
  | cons row rest ih => simp only [lookupWord, List.map_cons, ho.select, Word64.eq_map ho ha, ho.const, ih]

include ho ha in
theorem writeStack_map (enabled : B) (index tag : W) (stack : List W) :
    (writeStack o a enabled index tag stack).map fw = writeStack o' a' (f enabled) (fw index) (fw tag) (stack.map fw) := by
  simp only [writeStack, List.zipIdx_map, List.map_map, Function.comp_def, ho.select,
    ha.and, Word64.eq_map ho ha, ho.const, Prod.map_fst, Prod.map_snd, id_eq]

include ho ha in
theorem writeFields_map (enabled : B) (tag : W) (decoded : Decoded B W) (fields : List (Field B W)) :
    (writeFields o a enabled tag decoded fields).map (Field.map f fw) =
      writeFields o' a' (f enabled) (fw tag) (decoded.map f fw) (fields.map (Field.map f fw)) := by
  simp only [writeFields, List.zipIdx_map, List.map_map, Function.comp_def]
  congr 1
  funext x
  simp only [selectField, Field.map, Unpad.chooseByte_map ha, ho.select, ha.and,
    Word64.eq_map ho ha, ho.const, ha.const, Decoded.map, Prod.map_fst, Prod.map_snd, id_eq]

include ho ha in
theorem initializeFields_map (enabled : B) (tag : W) (fields : List (Field B W)) :
    (initializeFields o a enabled tag fields).map (Field.map f fw) =
      initializeFields o' a' (f enabled) (fw tag) (fields.map (Field.map f fw)) := by
  simp only [initializeFields, List.zipIdx_map, List.map_map, Function.comp_def]
  congr 1
  funext x
  simp only [selectField, Field.map, Unpad.chooseByte_map ha, ho.select, ha.and,
    Word64.eq_map ho ha, ho.const, ha.const, Prod.map_fst, Prod.map_snd, id_eq]

include ho ha in
theorem plan_map (capacity : Nat) (key payload : Decoded B W) (state : State B W) :
    (plan o a capacity key payload state).map f fw = plan o' a' capacity (key.map f fw) (payload.map f fw) (state.map f fw) := by
  simp only [plan, Plan.map, Decoded.map, State.map, ho.shift, ho.band, ho.const, ho.ule,
    ho.add, ho.sub, ho.select, Word64.eq_map ho ha, Word64.bor_map ha, ha.and, ha.not,
    Unpad.chooseByte_map ha, lookupWord_map ho ha]

include ho ha in
theorem planWithCursor_map (capacity position : Nat) (lastClear : B)
    (key payload : Decoded B W) (state : State B W) :
    (planWithCursor o a capacity position lastClear key payload state).map f fw =
      planWithCursor o' a' capacity position (f lastClear) (key.map f fw) (payload.map f fw) (state.map f fw) := by
  unfold planWithCursor
  rw [← plan_map ho ha]
  by_cases h : capacity > position + 10 <;> simp only [h,if_true,if_false,Plan.map,Decoded.map,State.map,ho.ule,ho.const,
    ho.add,ho.select,Word64.eq_map ho ha,Word64.bor_map ha,ha.and,ha.not,ha.const,
    Unpad.chooseByte_map ha]

include ho ha in
theorem applyPlan_map (position : Nat) (p : Plan B W) (state : State B W) :
    (applyPlan o a position p state).map f fw = applyPlan o' a' position (p.map f fw) (state.map f fw) := by
  simp only [applyPlan, State.map, Plan.map, ha.and, ha.not, Word64.eq_map ho ha, ho.const,
    ho.select, ho.add, ho.sub, writeStack_map ho ha, writeFields_map ho ha, initializeFields_map ho ha]

include ho ha in
theorem step_map (capacity : Nat) (decoders : List (Decoded B W)) (state : State B W) (position : Nat) :
    (step o a capacity decoders state position).map f fw =
      step o' a' capacity (decoders.map (Decoded.map f fw)) (state.map f fw) position := by
  have hg : (decoders[position]?.getD ⟨a.const 0, o.const position, o.const 0⟩).map f fw =
      (decoders.map (Decoded.map f fw))[position]?.getD ⟨a'.const 0, o'.const position, o'.const 0⟩ := by
    simp only [List.getElem?_map]
    cases decoders[position]? <;> simp [Decoded.map, ha.const, ho.const]
  have hs := congrArg Decoded.stop hg
  simp only [Decoded.map] at hs
  have hl : (decoders[capacity-1]?.getD ⟨a.const 0,o.const (capacity-1),o.const 0⟩).map f fw =
      (decoders.map (Decoded.map f fw))[capacity-1]?.getD ⟨a'.const 0,o'.const (capacity-1),o'.const 0⟩ := by
    simp only [List.getElem?_map]
    cases decoders[capacity-1]? <;> simp [Decoded.map,ha.const,ho.const]
  have hlo := congrArg Decoded.ok hl
  simp only [Decoded.map] at hlo
  simp only [step, applyPlan_map ho ha, planWithCursor_map ho ha, lookupDecoded_map ho ha, List.map_take, List.map_drop, hg, hs, hlo]

include hd ho ha in
theorem parseBody_map (wire : List B) :
    (parseBody d o a wire).map f fw = parseBody d' o' a' (wire.map f) := by
  have hf (positions : List Nat) (state : State B W) :
      (positions.foldl (step o a wire.length (table d o a wire)) state).map f fw =
        positions.foldl (step o' a' wire.length (table d' o' a' (wire.map f))) (state.map f fw) := by
    induction positions generalizing state with
    | nil => rfl
    | cons p rest ih =>
        simp only [List.foldl_cons, ih, step_map ho ha, table_map hd ho ha]
  simpa only [parseBody, List.length_map, initial_map ho ha] using hf (List.range wire.length) (initial o a wire.length)

include ho ha in
theorem completeMask_map (capacity : Nat) (state : State B W) :
    f (completeMask o a capacity state) = completeMask o' a' capacity (state.map f fw) := by
  simp [completeMask, State.map, ha.and, Word64.eq_map ho ha, ho.const]

include ho ha in
theorem getField_map (state : State B W) (index : Nat) :
    (getField o a state index).map f fw = getField o' a' (state.map f fw) index := by
  simp only [getField, State.map, List.getElem?_map]
  cases state.fields[index]? <;> simp [emptyField_map ho ha]

theorem body_map (wire : List B) : (body wire).map f = body (wire.map f) := by
  simp [body, MessageMac.content, List.map_take, List.map_drop]

include ho ha in
theorem ratchetRead_map (wire : List B) (state : State B W) :
    (ratchetRead o a wire state).map f = ratchetRead o' a' (wire.map f) (state.map f fw) := by
  have h := congrArg Field.offset (getField_map ho ha state 0)
  simp only [Field.map] at h
  simp only [ratchetRead, ReadAt.readCore_map ha, Word64.bytes_map ho, h]

include ho ha in
theorem acceptedMask_map (wire : List B) (state : State B W) :
    f (acceptedMask o a wire state) = acceptedMask o' a' (wire.map f) (state.map f fw) := by
  have hp (i) := congrArg Field.present (getField_map ho ha state i)
  have hl (i) := congrArg Field.length (getField_map ho ha state i)
  simp only [Field.map] at hp hl
  simp only [acceptedMask, List.length_map, ha.and, Receive.versionMask_map ha,
    completeMask_map ho ha, body_map, hp, hl, ho.ule, ho.const,
    ByteAuth.eqMask_map ha, OpenResult.get_map ha, ratchetRead_map ho ha, ha.const]
  split <;> simp [ha.const, body, MessageMac.content]

include ho ha in
theorem metadata_map (wire : List B) (state : State B W) :
    (metadata o a wire state).map f = metadata o' a' (wire.map f) (state.map f fw) := by
  have hp (i) := congrArg Field.present (getField_map ho ha state i)
  have hl (i) := congrArg Field.length (getField_map ho ha state i)
  have ho' (i) := congrArg Field.offset (getField_map ho ha state i)
  have hs (i) := congrArg Field.scalar (getField_map ho ha state i)
  simp only [Field.map] at hp hl ho' hs
  simp only [metadata, List.map_append, List.map_drop, List.map_cons, List.map_nil,
    ratchetRead_map ho ha, body_map, Word64.bytes_map ho, hp, hl, ho', hs, ha.and, ha.const]

include hd ho ha in
theorem parseCore_map (wire : List B) :
    (parseCore d o a wire).map f = parseCore d' o' a' (wire.map f) := by
  simp only [parseCore, List.map_cons, ByteAuth.release_map ha, acceptedMask_map ho ha,
    metadata_map ho ha, parseBody_map hd ho ha, body_map]

include hd ho ha in
theorem parseChecked_map (wire : List B) :
    (parseChecked d o a wire).map (List.map f) = parseChecked d' o' a' (wire.map f) := by
  simp only [parseChecked, List.length_map]
  split <;> simp [parseCore_map hd ho ha]
end Refinement

theorem ratchetRead_length (o : Word64.Ops B W) (a : ByteAuth.Ops B) (wire : List B) (state : State B W) :
    (ratchetRead o a wire state).length = 42 := by
  simp [ratchetRead, ReadAt.readCore_length, Word64.bytes_length]

theorem metadata_length (o : Word64.Ops B W) (a : ByteAuth.Ops B) (wire : List B) (state : State B W) :
    (metadata o a wire state).length = 89 := by simp [metadata, ratchetRead_length, Word64.bytes_length]

theorem parseCore_length (d : VarintDecode.Spqr.Ops B W) (o : Word64.Ops B W) (a : ByteAuth.Ops B) (wire : List B) :
    (parseCore d o a wire).length = 90 := by simp [parseCore, ByteAuth.release, metadata_length]

theorem compiled_parseCore_correct (wire : List (BVExpr 8)) (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (parseCore VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic wire).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (parseCore VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic wire))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (parseCore VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic wire))).vec.get index hi)) =
      (ByteCircuit.joinValue (parseCore VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
        (wire.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,
    parseCore_map (VarintDecode.Spqr.evaluationHom assign) (Word64.evaluationHom assign) (ByteAuth.evaluationHom assign)]

end TlsMpc.Signal.ProtoParse
