import TlsMpc.TlsWebSocketUpgrade
namespace TlsMpc.TlsWebSocketRemask
open TlsWebSocketUpgrade (get activity get_map activity_map)
open Std.Tactic.BVDecide
def all (a : ByteAuth.Ops B) : List B → B
 | [] => a.const 255
 | x::xs => a.and x (all a xs)
-- Supported profile: FIN binary, masked, canonical16bit length (payload≥126).
def lengthMatch (a : ByteAuth.Ops B) (hi lo wh wl : B) : Nat → Nat → B
 | _,0 => a.const 0
 | offset,n+1 =>
   let here := if 134≤offset then a.and (TlsPrivateSeal.eqLength a hi lo offset)
       (TlsPrivateSeal.eqLength a wh wl (offset-8)) else a.const 0
   TlsPrivateSeal.orMask a here (lengthMatch a hi lo wh wl (offset+1) n)
def padding (a : ByteAuth.Ops B) : List B → List B → B
 | [],[] => a.const 255
 | x::xs,m::ms => a.and (ByteAuth.eqMask a (a.and (a.not m) x) (a.const 0)) (padding a xs ms)
 | _,_ => a.const 0
def remask (a : ByteAuth.Ops B) (data masks fresh : List B) : List B :=
 (List.range data.length).map fun i =>
   let byte := if i<4 then get a data i else if i<8 then get a fresh (i-4)
     else a.xor (a.xor (get a data i) (get a data (4+(i-8)%4))) (get a fresh ((i-8)%4))
   a.and (get a masks i) byte
-- account resumability, producer validity, BE16 length, capacity data, fresh4.
def run (a : ByteAuth.Ops B) (capacity : Nat) (raw : List B) : List B :=
 let data := (raw.drop 4).take capacity
 let hi := get a raw 2; let lo := get a raw 3
 let active := activity a hi lo 0 capacity
 let valid := all a [ByteAuth.eqMask a (get a raw 0) (a.const 255),
   ByteAuth.eqMask a (get a raw 1) (a.const 255),active.1,
   ByteAuth.eqMask a (get a data 0) (a.const 130),ByteAuth.eqMask a (get a data 1) (a.const 254),
   lengthMatch a hi lo (get a data 2) (get a data 3) 0 (capacity+1),padding a data active.2]
 valid :: ByteAuth.release a valid ([hi,lo] ++ remask a data active.2 ((raw.drop (4+capacity)).take 4))
section Mapping
variable {a : ByteAuth.Ops B} {b : ByteAuth.Ops C} {f : B → C} (h : ByteAuth.Hom a b f)
include h
theorem all_map (xs : List B) : f (all a xs)=all b (xs.map f) := by
 induction xs with
 | nil => simp [all,h.const]
 | cons x xs ih => simp [all,h.and,ih]
theorem lengthMatch_map (hi lo wh wl : B) (offset n : Nat) :
 f (lengthMatch a hi lo wh wl offset n)=lengthMatch b (f hi) (f lo) (f wh) (f wl) offset n := by
 induction n generalizing offset with
 | zero => simp [lengthMatch,h.const]
 | succ n ih =>
   by_cases bound : 134≤offset <;> simp [lengthMatch,bound,TlsPrivateSeal.orMask_map h,TlsPrivateSeal.eqLength_map h,h.and,h.const,ih]
theorem padding_map (xs masks : List B) : f (padding a xs masks)=padding b (xs.map f) (masks.map f) := by
 induction xs generalizing masks with
 | nil => cases masks <;> simp [padding,h.const]
 | cons x xs ih => cases masks <;> simp [padding,h.const,h.and,h.not,ByteAuth.eqMask_map h,ih]
theorem remask_map (data masks fresh : List B) :
 (remask a data masks fresh).map f=remask b (data.map f) (masks.map f) (fresh.map f) := by
 simp only [remask,List.length_map,List.map_map,Function.comp_def]
 congr 1;funext i
 split <;> simp only [get_map h,h.and]
 all_goals split <;> simp [get_map h,h.and,h.xor]
theorem run_map (capacity : Nat) (raw : List B) :
 (run a capacity raw).map f=run b capacity (raw.map f) := by
 have active := activity_map h (get a raw 2) (get a raw 3) 0 capacity
 have first := congrArg Prod.fst active
 have rest := congrArg Prod.snd active
 simp only [Prod.fst,Prod.snd] at first rest
 simp only [run,List.map_cons,ByteAuth.release_map h,List.map_append,List.map_take,List.map_drop,
   List.map_cons,List.map_nil,all_map h,ByteAuth.eqMask_map h,h.const,get_map h,first,
   lengthMatch_map h,padding_map h,remask_map h,rest]
end Mapping
theorem run_length (a : ByteAuth.Ops B) (capacity : Nat) (raw : List B)
    (size : raw.length=capacity+8) : (run a capacity raw).length=capacity+3 := by
  simp only [run,List.length_cons,ByteAuth.release,List.length_map,List.length_append,
    List.length_cons,List.length_nil,remask,List.length_range,List.length_take,List.length_drop]
  omega

-- Fresh masking changes transport bytes but exactly preserves unmasked bytes.
theorem unmasked_unchanged (old oldMask fresh : BitVec 8) :
 (((old ^^^ oldMask) ^^^ fresh) ^^^ fresh) = old ^^^ oldMask := by
 simp [BitVec.xor_assoc]
theorem compiled_correct (capacity : Nat) (raw : List (BVExpr 8)) (assign : BVExpr.Assignment)
 (index : Nat) (bound : index<8*(run ByteAuth.symbolic capacity raw).length) :
 AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (run ByteAuth.symbolic capacity raw))).aig)
 (fun varId bit => (assign.get varId).bv.getLsbD bit)
 (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (run ByteAuth.symbolic capacity raw))).vec.get index bound)) =
 (ByteCircuit.joinValue (run ByteAuth.concrete capacity (raw.map (BVExpr.eval assign)))).getLsbD index := by
 rw [ByteCircuit.compile_bytes_correct,run_map (ByteAuth.evaluationHom assign)]
end TlsMpc.TlsWebSocketRemask

#print axioms TlsMpc.TlsWebSocketRemask.compiled_correct
#print axioms TlsMpc.TlsWebSocketRemask.unmasked_unchanged

#print axioms TlsMpc.TlsWebSocketRemask.run_length
