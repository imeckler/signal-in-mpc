import TlsMpc.Signal.PrivateInitialSpqrV1
namespace TlsMpc.Signal.PrivateInitialSpqrV1
open Std.Tactic.BVDecide
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
section
variable {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'}
 {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} {fw : W → W'}
 (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)

theorem part_map (xs : List B) (offset count : Nat) :
 (part xs offset count).map f = part (xs.map f) offset count := by
 simp only [part,List.map_take,List.map_drop]
theorem State.bytes_map (x : State B) : x.bytes.map f = (x.map f).bytes := by
 simp only [State.bytes,State.map,List.map_append,List.map_cons,List.map_nil]
include ha in
theorem State.parse_map (raw : List B) :
 (State.parse a raw).map f = State.parse a' (raw.map f) := by
 simp only [State.parse,State.map,part_map,OpenResult.get_map ha]
include ha in
theorem State.select_map (mask : B) (yes no : State B) :
 (State.select a mask yes no).map f = State.select a' (f mask) (yes.map f) (no.map f) := by
 simp only [State.select,State.map,Unpad.choose_map ha,Unpad.chooseByte_map ha]
include ha in
theorem literal_map (ns : List Nat) : (literal a ns).map f = literal a' ns := by
 simp only [literal,List.map_map,Function.comp_def,ha.const]
include ha in
theorem field_map (tag : Nat) (body : List B) :
 (field a tag body).map f = field a' tag (body.map f) := by
 simp only [field,List.length_map,List.map_append,literal_map ha]
include ha in
theorem serialize_map (x : State B) :
 (serialize a x).map f = serialize a' (x.map f) := by
 simp only [serialize,List.map_append,field_map ha,literal_map ha,State.map,
  List.map_cons,List.map_nil,ha.const,List.map_flatMap,List.map_map,Function.comp_def,part_map]
include hs in
theorem chainStart_map (auth : List B) :
 (chainStart s auth).map f = chainStart s' (auth.map f) := by
 simp only [chainStart,TlsKdf.expandFast_correct,TlsKdf.expandCore_map hs,
  TlsKdf.extract_map hs,TlsKdf.zeros_map hs,List.map_map,Function.comp_def,hs.byteConst]
include hs in
theorem authenticator_map (auth : List B) :
 (authenticator s auth).map f = authenticator s' (auth.map f) := by
 simp only [authenticator,TlsKdf.expandFast_correct,TlsKdf.expandCore_map hs,
  TlsKdf.extract_map hs,TlsKdf.zeros_map hs,List.map_append,List.map_replicate,List.map_cons,
  List.map_nil,List.map_map,Function.comp_def,hs.byteConst]
include hs in
theorem headerMac_map (key header : List B) :
 (headerMac s key header).map f = headerMac s' (key.map f) (header.map f) := by
 simp only [headerMac,Sha256.hmac_map hs,List.map_append,List.map_replicate,List.map_cons,
  List.map_nil,List.map_map,Function.comp_def,hs.byteConst]
include hs ha in
theorem start_map (auth generated : List B) :
 (start s a auth generated).map f = start s' a' (auth.map f) (generated.map f) := by
 simp only [start,List.length_map]
 split <;> simp only [List.map_cons,List.map_nil,ByteAuth.release_map ha,ha.and,ha.const,
  ByteAuth.eqMask_map ha,ByteAuth.equalMask_map ha,OpenResult.get_map ha,part_map,
  chainStart_map hs,authenticator_map hs,List.map_take,List.map_drop,List.map_append,
  headerMac_map hs,SpqrChain.materialFast_map hs ha,List.map_replicate,State.bytes,literal_map ha]
include hs ha in
theorem second_map (old : List B) :
 (second s a old).map f = second s' a' (old.map f) := by
 simp only [second,List.length_map]
 split <;> simp only [State.bytes,State.select,State.parse,List.map_cons,List.map_nil,
  List.map_append,Unpad.choose_map ha,Unpad.chooseByte_map ha,ByteAuth.release_map ha,
  ha.and,ha.const,ByteAuth.eqMask_map ha,OpenResult.get_map ha,List.map_drop,
  List.map_take,part_map,literal_map ha,SpqrChain.materialFast_map hs ha]

end

theorem compiled_start_correct (auth generated : List (BVExpr 8))
 (assign : BVExpr.Assignment) (index : Nat)
 (hi : index < 8*(start Sha256.symbolic ByteAuth.symbolic auth generated).length) :
 AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
  (start Sha256.symbolic ByteAuth.symbolic auth generated))).aig)
  (fun varId bit => (assign.get varId).bv.getLsbD bit)
  (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
   (start Sha256.symbolic ByteAuth.symbolic auth generated))).vec.get index hi)) =
 (ByteCircuit.joinValue (start Sha256.concrete ByteAuth.concrete
   (auth.map (BVExpr.eval assign)) (generated.map (BVExpr.eval assign)))).getLsbD index := by
 rw [ByteCircuit.compile_bytes_correct,start_map (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]

theorem compiled_second_correct (old : List (BVExpr 8))
 (assign : BVExpr.Assignment) (index : Nat)
 (hi : index < 8*(second Sha256.symbolic ByteAuth.symbolic old).length) :
 AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
  (second Sha256.symbolic ByteAuth.symbolic old))).aig)
  (fun varId bit => (assign.get varId).bv.getLsbD bit)
  (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
   (second Sha256.symbolic ByteAuth.symbolic old))).vec.get index hi)) =
 (ByteCircuit.joinValue (second Sha256.concrete ByteAuth.concrete
   (old.map (BVExpr.eval assign)))).getLsbD index := by
 rw [ByteCircuit.compile_bytes_correct,second_map (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]
end TlsMpc.Signal.PrivateInitialSpqrV1
