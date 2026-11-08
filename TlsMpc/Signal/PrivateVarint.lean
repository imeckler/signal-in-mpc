import TlsMpc.Signal.PrivateBuffer
import TlsMpc.Signal.Varint64

/-! Canonical variable-width varints with private BE16 length, independent of
public width profiles. The public capacity is five or ten bytes; unused tail
bytes are zero. Used for counters and nested byte-string length fields. -/
namespace TlsMpc.Signal.PrivateVarint
open Std.Tactic.BVDecide

def active (a : ByteAuth.Ops B) (groups : List B) (i : Nat) : B :=
  if i=0 then a.const 255 else a.not (ByteAuth.equalMask a (groups.drop i)
    (List.replicate (groups.length-i) (a.const 0)))

def countLoop (a : ByteAuth.Ops B) (groups : List B) : List Nat → List B → List B
  | [],bits => bits
  | i::is,bits =>
    let one := active a groups i :: List.replicate 15 (a.const 0)
    countLoop a groups is (PrivateBuffer.addLoop a bits one (List.range 16) (a.const 0)).1

def fromGroups (a : ByteAuth.Ops B) (groups : List B) : PrivateBuffer.Buffer B :=
  let bits := countLoop a groups (List.range groups.length) (PrivateBuffer.publicLength a 0)
  let data := (List.range groups.length).map (fun i =>
    a.and (active a groups i) (a.xor (OpenResult.get a groups i)
      (if i+1<groups.length then a.and (active a groups (i+1)) (a.const 128) else a.const 0)))
  PrivateBuffer.make a groups.length bits data

def uint32 (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (word : W) : PrivateBuffer.Buffer B :=
  fromGroups a (Varint.groups s a word)

def uint64 (v : Varint64.Ops B W) (a : ByteAuth.Ops B) (word : W) : PrivateBuffer.Buffer B :=
  fromGroups a (Varint64.groups v word)

section Refinement
variable {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} (ha : ByteAuth.Hom a a' f)
include ha

theorem active_map (groups : List B) (i : Nat) : f (active a groups i) = active a' (groups.map f) i := by
  simp only [active,List.length_map]
  split <;> simp only [ha.const,ha.not,ByteAuth.equalMask_map ha,List.map_drop,List.map_replicate]
theorem countLoop_map (groups : List B) (is : List Nat) (bits : List B) :
    (countLoop a groups is bits).map f = countLoop a' (groups.map f) is (bits.map f) := by
  induction is generalizing bits with
  | nil => rfl
  | cons i is ih =>
    simp only [countLoop,ih]
    have mapped := congrArg Prod.fst (PrivateBuffer.addLoop_map ha bits
      (active a groups i::List.replicate 15 (a.const 0)) (List.range 16) (a.const 0))
    apply congrArg (countLoop a' (groups.map f) is)
    simpa only [List.map_cons,List.map_replicate,active_map ha,ha.const] using mapped

theorem fromGroups_map (groups : List B) :
    (fromGroups a groups).map f = fromGroups a' (groups.map f) := by
  simp only [fromGroups,PrivateBuffer.make_map ha,countLoop_map ha,PrivateBuffer.publicLength_map ha,
    List.length_map,List.map_map,Function.comp_def,ha.and,ha.xor,active_map ha,OpenResult.get_map ha]
  congr 1;congr 1;funext i
  split <;> simp_all only [ha.and,active_map ha,ha.const]
end Refinement
theorem uint32_map {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'}
    {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} {fw : W → W'}
    (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f) (word : W) :
    (uint32 s a word).map f = uint32 s' a' (fw word) := by
  simp only [uint32,fromGroups_map ha,Varint.groups_map hs ha]

theorem uint64_map {v : Varint64.Ops B W} {v' : Varint64.Ops B' W'}
    {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} {fw : W → W'}
    (hv : Varint64.Hom v v' f fw) (ha : ByteAuth.Hom a a' f) (word : W) :
    (uint64 v a word).map f = uint64 v' a' (fw word) := by
  simp only [uint64,fromGroups_map ha,Varint64.groups_map hv]

theorem compiled_uint32_correct (word : BVExpr 32) (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8*(PrivateBuffer.output ByteAuth.symbolic (uint32 Sha256.symbolic ByteAuth.symbolic word)).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (PrivateBuffer.output ByteAuth.symbolic (uint32 Sha256.symbolic ByteAuth.symbolic word)))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (PrivateBuffer.output ByteAuth.symbolic (uint32 Sha256.symbolic ByteAuth.symbolic word)))).vec.get index hi)) =
    (ByteCircuit.joinValue (PrivateBuffer.output ByteAuth.concrete (uint32 Sha256.concrete ByteAuth.concrete
      (word.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,PrivateBuffer.output_map (ByteAuth.evaluationHom assign),
    uint32_map (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]

theorem compiled_uint64_correct (word : BVExpr 64) (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8*(PrivateBuffer.output ByteAuth.symbolic (uint64 Varint64.symbolic ByteAuth.symbolic word)).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (PrivateBuffer.output ByteAuth.symbolic (uint64 Varint64.symbolic ByteAuth.symbolic word)))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (PrivateBuffer.output ByteAuth.symbolic (uint64 Varint64.symbolic ByteAuth.symbolic word)))).vec.get index hi)) =
    (ByteCircuit.joinValue (PrivateBuffer.output ByteAuth.concrete (uint64 Varint64.concrete ByteAuth.concrete
      (word.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,PrivateBuffer.output_map (ByteAuth.evaluationHom assign),
    uint64_map (Varint64.evaluationHom assign) (ByteAuth.evaluationHom assign)]

end TlsMpc.Signal.PrivateVarint
