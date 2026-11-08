import TlsMpc.Signal.PrivateProtoParseV1
namespace TlsMpc.Signal.PrivateProtoParseV1
open ProtoParse Word64 Std.Tactic.BVDecide
section Refinement
variable {d : VarintDecode.Spqr.Ops B W} {d' : VarintDecode.Spqr.Ops B' W'}
  {o : Word64.Ops B W} {o' : Word64.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {fw : W → W'}
  (hd : VarintDecode.Spqr.Hom d d' f fw) (ho : Word64.Hom o o' f fw) (ha : ByteAuth.Hom a a' f)

include ho ha in
theorem boundedBytes_map (ending : W) (bytes : List B) :
    (boundedBytes o a ending bytes).map f = boundedBytes o' a' (fw ending) (bytes.map f) := by
  simp only [boundedBytes,List.zipIdx_map,List.map_map,Function.comp_def,Unpad.chooseByte_map ha,
    ho.ule,ho.const,ha.const,Prod.map_fst,Prod.map_snd,id_eq]

include hd ho ha in
theorem table_map (ending : W) (bytes : List B) :
    (table d o a ending bytes).map (Decoded.map f fw) = table d' o' a' (fw ending) (bytes.map f) := by
  simp only [table,ProtoParse.table_map hd ho ha,boundedBytes_map ho ha]

include ho ha in
theorem plan_map (ending : W) (key payload : Decoded B W) (state : State B W) :
    (plan o a ending key payload state).map f fw =
      plan o' a' (fw ending) (key.map f fw) (payload.map f fw) (state.map f fw) := by
  simp only [plan,Plan.map,Decoded.map,State.map,ho.shift,ho.band,ho.const,ho.ule,
    ho.add,ho.sub,ho.select,Word64.eq_map ho ha,Word64.bor_map ha,ha.and,ha.not,
    Unpad.chooseByte_map ha,ProtoParse.lookupWord_map ho ha]

include ho ha in
theorem planWithCursor_map (ending : W) (position : Nat) (lastClear : B)
    (key payload : Decoded B W) (state : State B W) :
    (planWithCursor o a ending position lastClear key payload state).map f fw =
      planWithCursor o' a' (fw ending) position (f lastClear) (key.map f fw) (payload.map f fw) (state.map f fw) := by
  unfold planWithCursor
  rw [←plan_map ho ha]
  simp only [Plan.map,Decoded.map,State.map,ho.ule,ho.const,ho.add,ho.select,
    Word64.eq_map ho ha,Word64.bor_map ha,ha.and,ha.not,ha.const,Unpad.chooseByte_map ha]

include ho ha in
theorem applyPlan_map (ending : W) (position : Nat) (p : Plan B W) (state : State B W) :
    (applyPlan o a ending position p state).map f fw =
      applyPlan o' a' (fw ending) position (p.map f fw) (state.map f fw) := by
  simp only [applyPlan,State.map,Plan.map,ha.and,ha.not,Word64.eq_map ho ha,ho.const,
    ho.select,ho.add,ho.sub,ho.ule,ProtoParse.writeStack_map ho ha,
    ProtoParse.writeFields_map ho ha,ProtoParse.initializeFields_map ho ha]

include ho ha in
theorem selectState_map (mask : B) (yes no : State B W) :
    (selectState o a mask yes no).map f fw =
      selectState o' a' (f mask) (yes.map f fw) (no.map f fw) := by
  simp only [selectState,State.map,Unpad.chooseByte_map ha,ho.select,
    List.map_zipWith,List.zipWith_map,ProtoParse.selectField_map ho ha]

include ho ha in
theorem step_map (ending : W) (rows : List (Decoded B W)) (state : State B W) (position : Nat) :
    (step o a ending rows state position).map f fw =
      step o' a' (fw ending) (rows.map (Decoded.map f fw)) (state.map f fw) position := by
  have hg : (rows[position]?.getD ⟨a.const 0,o.const position,o.const 0⟩).map f fw =
      (rows.map (Decoded.map f fw))[position]?.getD ⟨a'.const 0,o'.const position,o'.const 0⟩ := by
    simp only [List.getElem?_map]
    cases rows[position]? <;> simp [Decoded.map,ha.const,ho.const]
  have hs := congrArg Decoded.stop hg
  simp only [Decoded.map] at hs
  have hl := ProtoParse.lookupDecoded_map ho ha (o.sub ending (o.const 1)) 0 rows
  have hlo := congrArg Decoded.ok hl
  simp only [Decoded.map,ho.sub,ho.const] at hlo
  simp only [step,selectState_map ho ha,applyPlan_map ho ha,planWithCursor_map ho ha,
    ProtoParse.lookupDecoded_map ho ha,List.map_take,List.map_drop,hg,hs,hlo,ho.ule,ho.const]

include hd ho ha in
theorem parseBody_map (ending : W) (bytes : List B) :
    (parseBody d o a ending bytes).map f fw = parseBody d' o' a' (fw ending) (bytes.map f) := by
  have fold (positions : List Nat) (state : State B W) :
      (positions.foldl (step o a ending (table d o a ending bytes)) state).map f fw =
        positions.foldl (step o' a' (fw ending) (table d' o' a' (fw ending) (bytes.map f))) (state.map f fw) := by
    induction positions generalizing state with
    | nil => rfl
    | cons position rest ih => simp only [List.foldl_cons,ih,step_map ho ha,table_map hd ho ha]
  simpa only [parseBody,List.length_map,ProtoParse.initial_map ho ha] using
    fold (List.range bytes.length) (initial o a bytes.length)

include ho ha in
theorem completeMask_map (ending : W) (state : State B W) :
    f (completeMask o a ending state) = completeMask o' a' (fw ending) (state.map f fw) := by
  simp [completeMask,State.map,ha.and,Word64.eq_map ho ha,ho.const]

include ho ha in
theorem ratchetRead_map (ending : W) (bytes : List B) (state : State B W) :
    (ratchetRead o a ending bytes state).map f = ratchetRead o' a' (fw ending) (bytes.map f) (state.map f fw) := by
  have offset := congrArg Field.offset (ProtoParse.getField_map ho ha state 0)
  simp only [Field.map] at offset
  simp only [ratchetRead,PrivateReadAtV1.read_map ho ha,offset]

include ho ha in
theorem metadata_map (ending : W) (wire : List B) (state : State B W) :
    (metadata o a ending wire state).map f = metadata o' a' (fw ending) (wire.map f) (state.map f fw) := by
  have present (i) := congrArg Field.present (ProtoParse.getField_map ho ha state i)
  have length (i) := congrArg Field.length (ProtoParse.getField_map ho ha state i)
  have offset (i) := congrArg Field.offset (ProtoParse.getField_map ho ha state i)
  have scalar (i) := congrArg Field.scalar (ProtoParse.getField_map ho ha state i)
  simp only [Field.map] at present length offset scalar
  simp only [metadata,List.map_append,List.map_drop,List.map_cons,List.map_nil,
    ratchetRead_map ho ha,ProtoParse.body_map,Word64.bytes_map ho,present,length,offset,scalar,ha.and,ha.const]

include hd ho ha in
theorem parse_map (wire : List B) (lengthHigh lengthLow upstreamValid : B) :
    (parse d o a wire lengthHigh lengthLow upstreamValid).map f fw =
      parse d' o' a' (wire.map f) (f lengthHigh) (f lengthLow) (f upstreamValid) := by
  have present (state : State B W) (index) := congrArg Field.present (ProtoParse.getField_map ho ha state index)
  have length (state : State B W) (index) := congrArg Field.length (ProtoParse.getField_map ho ha state index)
  simp only [Field.map] at present length
  simp only [parse,Parsed.map,parseBody_map hd ho ha,ProtoParse.body_map,List.length_map,
    metadata_map ho ha,ByteAuth.release_map ha,ha.and,ha.const,
    Receive.versionMask_map ha,completeMask_map ho ha,ByteAuth.eqMask_map ha,ho.ule,ho.const,
    ho.pack,ho.select,ho.sub,List.map_append,List.map_replicate,List.map_cons,List.map_nil,
    present,length,ratchetRead_map ho ha,OpenResult.get_map ha]

include hd ho ha in
theorem parseCore_map (wire : List B) (lengthHigh lengthLow upstreamValid : B) :
    (parseCore d o a wire lengthHigh lengthLow upstreamValid).map f =
      parseCore d' o' a' (wire.map f) (f lengthHigh) (f lengthLow) (f upstreamValid) := by
  have h := parse_map hd ho ha wire lengthHigh lengthLow upstreamValid
  have valid := congrArg Parsed.valid h
  have metadata := congrArg Parsed.metadata h
  simp only [Parsed.map] at valid metadata
  simp only [parseCore,List.map_cons,valid,metadata]
end Refinement

theorem metadata_length (o : Word64.Ops B W) (a : ByteAuth.Ops B) (ending : W)
    (wire : List B) (state : State B W) : (metadata o a ending wire state).length = 89 := by
  simp [metadata,ratchetRead,PrivateReadAtV1.read_length,Word64.bytes_length]

theorem parseCore_length (d : VarintDecode.Spqr.Ops B W) (o : Word64.Ops B W) (a : ByteAuth.Ops B)
    (wire : List B) (lengthHigh lengthLow upstreamValid : B) :
    (parseCore d o a wire lengthHigh lengthLow upstreamValid).length = 90 := by
  simp [parseCore,parse,ByteAuth.release,metadata_length]

/-- Factor the compiler's dependent vector type once over an arbitrary byte
list, avoiding elaboration-time expansion of the whole parser expression. -/
def compiledBit (bytes : List (BVExpr 8)) (assign : BVExpr.Assignment) (index : Nat)
    (inside : index < 8 * bytes.length) : Bool :=
  AigExport.evalRef
    (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr bytes)).aig)
    (fun varId bit => (assign.get varId).bv.getLsbD bit)
    (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr bytes)).vec.get index inside))

theorem compiledBit_correct (bytes : List (BVExpr 8)) (assign : BVExpr.Assignment) (index : Nat)
    (inside : index < 8 * bytes.length) :
    compiledBit bytes assign index inside =
      (ByteCircuit.joinValue (bytes.map (BVExpr.eval assign))).getLsbD index :=
  ByteCircuit.compile_bytes_correct bytes assign index inside

theorem compiled_parseCore_correct (wire : List (BVExpr 8))
    (lengthHigh lengthLow upstreamValid : BVExpr 8) (assign : BVExpr.Assignment) (index : Nat)
    (inside : index < 8 * (parseCore VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic
      wire lengthHigh lengthLow upstreamValid).length) :
    compiledBit (parseCore VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic
      wire lengthHigh lengthLow upstreamValid) assign index inside =
      (ByteCircuit.joinValue (parseCore VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
        (wire.map (BVExpr.eval assign)) (BVExpr.eval assign lengthHigh)
        (BVExpr.eval assign lengthLow) (BVExpr.eval assign upstreamValid))).getLsbD index := by
  rw [compiledBit_correct,
    parseCore_map (VarintDecode.Spqr.evaluationHom assign) (Word64.evaluationHom assign)
      (ByteAuth.evaluationHom assign)]

#print axioms parse_map
#print axioms parseCore_map
#print axioms TlsMpc.Signal.PrivateProtoParseV1.compiled_parseCore_correct

end TlsMpc.Signal.PrivateProtoParseV1
