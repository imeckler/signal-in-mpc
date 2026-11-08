import ProtoParseWork.FullParserV3Work.Observed
open TlsMpc TlsMpc.Signal
set_option linter.unusedSimpArgs false
namespace FullParserV3.Observed
section Hom
variable {d : VarintDecode.Spqr.Ops B W} {d' : VarintDecode.Spqr.Ops B' W'}
  {o : Word64.Ops B W} {o' : Word64.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {fw : W → W'}
  (hd : VarintDecode.Spqr.Hom d d' f fw) (ho : Word64.Hom o o' f fw) (ha : ByteAuth.Hom a a' f)

include ho ha in
theorem classify_map (key payload : ProtoParse.Decoded B W) (state : ProtoParse.State B W) :
    (classify o a key payload state).map fw = classify o' a' (key.map f fw) (payload.map f fw) (state.map f fw) := by
  simp only [classify,ErrorMeta.map,ProtoParse.Decoded.map,ProtoParse.State.map,
    ho.shift,ho.band,ho.const,ho.ule,ho.add,ho.select,Word64.eq_map ho ha,Word64.bor_map ha,
    Unpad.chooseByte_map ha,ha.and,ha.not]

include ho ha in
theorem finish_map (state : State B W) :
    (finish o a state).map f fw = finish o' a' (state.map f fw) := by
  simp only [finish,State.map,ErrorMeta.map,ProtoParse.State.map,
    ho.const,ho.select,Word64.eq_map ho ha,ha.and,ha.not]

include ho ha in
theorem step_map (capacity : Nat) (rows : List (ProtoParse.Decoded B W)) (state : State B W) (position : Nat) :
    (step o a capacity rows state position).map f fw =
      step o' a' capacity (rows.map (ProtoParse.Decoded.map f fw)) (state.map f fw) position := by
  have hget (i : Nat) : (rows[i]?.getD ⟨a.const 0,o.const i,o.const 0⟩).map f fw =
      (rows.map (ProtoParse.Decoded.map f fw))[i]?.getD ⟨a'.const 0,o'.const i,o'.const 0⟩ := by
    simp only [List.getElem?_map]
    cases rows[i]? <;> simp [ProtoParse.Decoded.map,ha.const,ho.const]
  have hkey := hget position
  have hstop := congrArg ProtoParse.Decoded.stop hkey
  have hlast := congrArg ProtoParse.Decoded.ok (hget (capacity-1))
  simp only [ProtoParse.Decoded.map] at hstop hlast
  let key := rows[position]?.getD ⟨a.const 0,o.const position,o.const 0⟩
  let payload := ProtoParse.lookupDecoded o a key.stop (position+1) ((rows.drop (position+1)).take 10)
  let last := (rows[capacity-1]?.getD ⟨a.const 0,o.const (capacity-1),o.const 0⟩).ok
  have hc := classify_map ho ha key payload state.parser
  have hcode := congrArg ErrorMeta.code hc
  have hparameter := congrArg ErrorMeta.parameter hc
  have hp := congrArg ProtoParse.Plan.ok (ProtoParse.planWithCursor_map ho ha capacity position last key payload state.parser)
  simp only [ErrorMeta.map,ProtoParse.Plan.map,key,payload,last,ProtoParse.lookupDecoded_map ho ha,
    List.map_take,List.map_drop,hkey,hstop,hlast] at hcode hparameter hp
  simp only [step,State.map,ErrorMeta.map,ProtoParse.step_map ho ha,
    ho.select,Word64.eq_map ho ha,ho.const,ha.and,ha.not,hcode,hparameter,hp]
  rfl

include hd ho ha in
theorem parse_map (body : List B) :
    (parse d o a body).map f fw = parse d' o' a' (body.map f) := by
  have h (positions : List Nat) (state : State B W) :
      (positions.foldl (step o a body.length (ProtoParse.table d o a body)) state).map f fw =
      positions.foldl (step o' a' body.length (ProtoParse.table d' o' a' (body.map f))) (state.map f fw) := by
    induction positions generalizing state with
    | nil => rfl
    | cons pos rest ih => simpa only [List.foldl_cons,step_map ho ha,ProtoParse.table_map hd ho ha] using ih (step o a body.length (ProtoParse.table d o a body) state pos)
  unfold parse
  simp only [List.length_map]
  rw [finish_map ho ha,h]
  simp only [State.map,ErrorMeta.map,ProtoParse.initial_map ho ha,ho.const]
end Hom

#print axioms classify_map
#print axioms step_map
#print axioms parse_map
end FullParserV3.Observed
