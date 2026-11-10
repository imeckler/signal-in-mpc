import TlsMpc.Signal.PreKeyBundle

/-! Pure validation-prefix outcome after typed bundle construction.
The external trust-store result is a shared code0=Ok(true),1=Ok(false),2=Err;
other codes conservatively map to callback error. No TOFU policy is defined.
Signature inputs here are INTERNAL outputs of the frozen XEdDSA computation,
not caller-provided authentication flags. PreKeyWork/adapter.py binds them.
Errors16=UntrustedIdentity,17=external trust error,18=SignatureValidationFailed.
The full callback error object/address stays at its separate store boundary.
All result bytes remain shared. This is not production PQXDH authorization. -/
namespace TlsMpc.Signal.PreKeyValidation
open Std.Tactic.BVDecide

def prefixError (a : ByteAuth.Ops B) (trust ecVerified pqVerified : B) : B :=
  Unpad.chooseByte a (ByteAuth.eqMask a trust (a.const 0))
    (Unpad.chooseByte a (ByteAuth.eqMask a ecVerified (a.const 255))
      (Unpad.chooseByte a (ByteAuth.eqMask a pqVerified (a.const 255)) (a.const 0) (a.const 18))
      (a.const 18))
    (Unpad.chooseByte a (ByteAuth.eqMask a trust (a.const 1)) (a.const 16) (a.const 17))

/-- Input constructed20, external trust1, computed EC status1, computed PQ
status1. Output status,error,optional-present,metadata17. Constructor failures
precede trust; trust precedes both signatures. No store load/write is performed. -/
def finish (a : ByteAuth.Ops B) (constructed : List B) (trust ecVerified pqVerified : B) : List B :=
  let missing := OpenResult.get a constructed 1
  let code := Unpad.chooseByte a (ByteAuth.eqMask a missing (a.const 0))
    (prefixError a trust ecVerified pqVerified) missing
  let ok := ByteAuth.eqMask a code (a.const 0)
  [ok,code] ++ ByteAuth.release a ok (constructed.drop 2)

section Refinement
variable {a : ByteAuth.Ops B} {b : ByteAuth.Ops B'} {f : B → B'} (h : ByteAuth.Hom a b f)
include h

theorem prefixError_map (trust ec pq : B) :
    f (prefixError a trust ec pq) = prefixError b (f trust) (f ec) (f pq) := by
  simp only [prefixError,Unpad.chooseByte_map h,ByteAuth.eqMask_map h,h.const]
theorem finish_map (constructed : List B) (trust ec pq : B) :
    (finish a constructed trust ec pq).map f = finish b (constructed.map f) (f trust) (f ec) (f pq) := by
  simp only [finish,List.map_append,List.map_cons,List.map_nil,ByteAuth.release_map h,List.map_drop,
    Unpad.chooseByte_map h,ByteAuth.eqMask_map h,h.const,OpenResult.get_map h,prefixError_map h]
end Refinement

theorem chooseEq_value (x y yes no : BitVec 8) :
    Unpad.chooseByte ByteAuth.concrete (ByteAuth.eqMask ByteAuth.concrete x y) yes no =
      if x = y then yes else no := by
  rw [ByteAuth.eqMask_value]
  split <;> simp only [Unpad.chooseByte_accept,Unpad.chooseByte_reject]

def prefixSpec (trust ec pq : BitVec 8) : BitVec 8 :=
  if trust = 0 then if ec = 255 then if pq = 255 then 0 else 18 else 18
  else if trust = 1 then 16 else 17

theorem prefixError_spec (trust ec pq : BitVec 8) :
    prefixError ByteAuth.concrete trust ec pq = prefixSpec trust ec pq := by
  simp only [prefixError,chooseEq_value]
  rfl

theorem finish_spec (constructed : List (BitVec 8)) (trust ec pq : BitVec 8) :
    finish ByteAuth.concrete constructed trust ec pq =
      let missing := OpenResult.get ByteAuth.concrete constructed 1
      let code := if missing = 0 then prefixSpec trust ec pq else missing
      [if code = 0 then 255 else 0,code] ++
        (if code = 0 then constructed.drop 2 else List.replicate (constructed.length-2) 0) := by
  simp only [finish]
  rw [chooseEq_value,prefixError_spec]
  simp only [ByteAuth.eqMask_value]
  have release_value (code : BitVec 8) (xs : List (BitVec 8)) :
      ByteAuth.release ByteAuth.concrete (if code = 0 then 255 else 0) xs =
        if code = 0 then xs else List.replicate xs.length 0 := by
    split <;> simp only [ByteAuth.release_accept,ByteAuth.release_reject]
  let code := if OpenResult.get ByteAuth.concrete constructed 1 = 0 then prefixSpec trust ec pq else OpenResult.get ByteAuth.concrete constructed 1
  change [if code = 0 then 255 else 0,code] ++ ByteAuth.release ByteAuth.concrete (if code = 0 then 255 else 0) (constructed.drop 2) = _
  rw [release_value code]
  simp only [List.length_drop]
  rfl

theorem compiled_finish_correct (constructed : List (BVExpr 8)) (trust ec pq : BVExpr 8)
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8*(finish ByteAuth.symbolic constructed trust ec pq).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (finish ByteAuth.symbolic constructed trust ec pq))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (finish ByteAuth.symbolic constructed trust ec pq))).vec.get index hi)) =
      (ByteCircuit.joinValue (finish ByteAuth.concrete (constructed.map (BVExpr.eval assign))
        (BVExpr.eval assign trust) (BVExpr.eval assign ec) (BVExpr.eval assign pq))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,finish_map (ByteAuth.evaluationHom assign)]
/-- Raw decode is outside the typed Rust operation. Code32 is explicitly a
local boundary failure, not an invented libsignal error or raw-parser ordering.
Individual key decoder errors are retained separately by the staged adapter. -/
def typedFinish (a : ByteAuth.Ops B) (wireStatuses constructed : List B) (trust ec pq : B) : List B :=
  let typed := ByteAuth.equalMask a wireStatuses (List.replicate wireStatuses.length (a.const 255))
  let candidate := finish a constructed trust ec pq
  Unpad.choose a typed candidate ([a.const 0,a.const 32] ++ List.replicate (candidate.length-2) (a.const 0))

theorem typedFinish_map {a : ByteAuth.Ops B} {b : ByteAuth.Ops B'} {f : B → B'}
    (h : ByteAuth.Hom a b f) (wireStatuses constructed : List B) (trust ec pq : B) :
    (typedFinish a wireStatuses constructed trust ec pq).map f =
      typedFinish b (wireStatuses.map f) (constructed.map f) (f trust) (f ec) (f pq) := by
  have hl := congrArg List.length (finish_map h constructed trust ec pq)
  simp only [List.length_map] at hl
  simp only [typedFinish,Unpad.choose_map h,ByteAuth.equalMask_map h,List.map_replicate,
    List.length_map,h.const,finish_map h,List.map_append,List.map_cons,List.map_nil,hl]

theorem compiled_typedFinish_correct (wireStatuses constructed : List (BVExpr 8)) (trust ec pq : BVExpr 8)
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8*(typedFinish ByteAuth.symbolic wireStatuses constructed trust ec pq).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (typedFinish ByteAuth.symbolic wireStatuses constructed trust ec pq))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (typedFinish ByteAuth.symbolic wireStatuses constructed trust ec pq))).vec.get index hi)) =
      (ByteCircuit.joinValue (typedFinish ByteAuth.concrete (wireStatuses.map (BVExpr.eval assign))
        (constructed.map (BVExpr.eval assign)) (BVExpr.eval assign trust) (BVExpr.eval assign ec) (BVExpr.eval assign pq))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,typedFinish_map (ByteAuth.evaluationHom assign)]

end TlsMpc.Signal.PreKeyValidation
