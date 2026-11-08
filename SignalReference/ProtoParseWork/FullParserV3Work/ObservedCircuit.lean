import ProtoParseWork.FullParserV3Work.ObservedProofs
open TlsMpc TlsMpc.Signal Std.Tactic.BVDecide
namespace FullParserV3.Observed
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def fieldBytes (o : Word64.Ops B W) (a : ByteAuth.Ops B) (state : ProtoParse.State B W) (i : Nat) : List B :=
  let field := ProtoParse.getField o a state i
  field.present :: (Word64.bytes o field.offset ++ Word64.bytes o field.length ++ Word64.bytes o field.scalar)

/-- Private proof-observation circuit: status, cursor, error constructor and
parameter, then all six unmasked field records. It is not a production export. -/
@[irreducible] def viewCore (d : VarintDecode.Spqr.Ops B W) (o : Word64.Ops B W) (a : ByteAuth.Ops B)
    (body : List B) : List B :=
  let state := parse d o a body
  ProtoParse.completeMask o a body.length state.parser ::
    (Word64.bytes o state.parser.next ++ Word64.bytes o state.error.code ++
      Word64.bytes o state.error.parameter ++ (List.range 6).flatMap (fieldBytes o a state.parser))

theorem fieldBytes_map {o : Word64.Ops B W} {o' : Word64.Ops B' W'}
    {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} {fw : W → W'}
    (ho : Word64.Hom o o' f fw) (ha : ByteAuth.Hom a a' f)
    (state : ProtoParse.State B W) (i : Nat) :
    (fieldBytes o a state i).map f = fieldBytes o' a' (state.map f fw) i := by
  have h := ProtoParse.getField_map ho ha state i
  have hp := congrArg ProtoParse.Field.present h
  have hoff := congrArg ProtoParse.Field.offset h
  have hl := congrArg ProtoParse.Field.length h
  have hs := congrArg ProtoParse.Field.scalar h
  simp only [ProtoParse.Field.map] at hp hoff hl hs
  simp only [fieldBytes,List.map_cons,List.map_append,Word64.bytes_map ho,hp,hoff,hl,hs]

theorem viewCore_map {d : VarintDecode.Spqr.Ops B W} {d' : VarintDecode.Spqr.Ops B' W'}
    {o : Word64.Ops B W} {o' : Word64.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
    {f : B → B'} {fw : W → W'}
    (hd : VarintDecode.Spqr.Hom d d' f fw) (ho : Word64.Hom o o' f fw) (ha : ByteAuth.Hom a a' f)
    (body : List B) :
    (viewCore d o a body).map f = viewCore d' o' a' (body.map f) := by
  unfold viewCore
  rw [←parse_map hd ho ha]
  simp only [State.map,ErrorMeta.map,List.length_map,List.map_cons,List.map_append,List.map_flatMap,
    ProtoParse.completeMask_map ho ha,Word64.bytes_map ho,fieldBytes_map ho ha]
  rfl

theorem fieldBytes_length (o : Word64.Ops B W) (a : ByteAuth.Ops B)
    (state : ProtoParse.State B W) (i : Nat) : (fieldBytes o a state i).length = 25 := by
  simp [fieldBytes,Word64.bytes_length]

theorem viewCore_length (d : VarintDecode.Spqr.Ops B W) (o : Word64.Ops B W) (a : ByteAuth.Ops B)
    (body : List B) : (viewCore d o a body).length = 175 := by
  simp [viewCore,Word64.bytes_length,List.length_flatMap,fieldBytes_length]
  decide

theorem compiled_viewCore_correct (body : List (BVExpr 8)) (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (viewCore VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic body).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (viewCore VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic body))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (viewCore VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic body))).vec.get index hi)) =
      (ByteCircuit.joinValue (viewCore VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
        (body.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,
    viewCore_map (VarintDecode.Spqr.evaluationHom assign) (Word64.evaluationHom assign) (ByteAuth.evaluationHom assign)]

#print axioms viewCore_map
#print axioms compiled_viewCore_correct
end FullParserV3.Observed
