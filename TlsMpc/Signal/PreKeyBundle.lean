import TlsMpc.Signal.OpenResult

/-! The pinned PreKeyBundleContent -> PreKeyBundle constructor prefix.
The eleven presence bytes represent Some by1 and None by0 (other values are
interpreted as absent, outside the canonical representation). They are shared.
Typed key/device decoding is a separate prior boundary, not reordered here.
Registration and all three key IDs retain their complete32 bits.
Optional ID/public-key mismatch is discarded by Option::zip, not an error. -/
namespace TlsMpc.Signal.PreKeyBundle
open Std.Tactic.BVDecide

/-- Field positions follow actual PreKeyBundleContent declaration order.
Error codes follow actual Rust argument evaluation order; identity is last. -/
def required : List (Nat × Nat) := [(0,1),(1,2),(4,3),(5,4),(6,5),(8,6),(9,7),(10,8),(7,9)]

def firstMissing (a : ByteAuth.Ops B) (flags : List B) : List (Nat × Nat) → B
  | [] => a.const 0
  | (i,code) :: rest => Unpad.chooseByte a
    (ByteAuth.eqMask a (OpenResult.get a flags i) (a.const 1))
    (firstMissing a flags rest) (a.const code)

def optionalMask (a : ByteAuth.Ops B) (flags : List B) : B :=
  a.and (ByteAuth.eqMask a (OpenResult.get a flags 2) (a.const 1))
    (ByteAuth.eqMask a (OpenResult.get a flags 3) (a.const 1))

/-- Metadata layout registrationBE4,device1,optionalIdBE4,signedIdBE4,PQIdBE4.
Only the optional ID disappears when its optional public key is absent. -/
def metadata (a : ByteAuth.Ops B) (flags raw : List B) : List B :=
  raw.take 5 ++ ByteAuth.release a (optionalMask a flags) ((raw.drop 5).take 4) ++ raw.drop 9

/-- status || first missing code || optional-present0/1 || metadata17.
Metadata is zero on a constructor error. This does not check signatures. -/
def construct (a : ByteAuth.Ops B) (flags raw : List B) : List B :=
  let missing := firstMissing a flags required
  let ok := ByteAuth.eqMask a missing (a.const 0)
  [ok,missing,a.and (a.and ok (optionalMask a flags)) (a.const 1)] ++
    ByteAuth.release a ok (metadata a flags raw)

section Refinement
variable {a : ByteAuth.Ops B} {b : ByteAuth.Ops B'} {f : B → B'} (h : ByteAuth.Hom a b f)
include h

theorem firstMissing_map (flags : List B) (fields : List (Nat × Nat)) :
    f (firstMissing a flags fields) = firstMissing b (flags.map f) fields := by
  induction fields with
  | nil => exact h.const 0
  | cons field rest ih => rcases field with ⟨i,code⟩; simp only [firstMissing,Unpad.chooseByte_map h,
      ByteAuth.eqMask_map h,OpenResult.get_map h,h.const,ih]
theorem optionalMask_map (flags : List B) : f (optionalMask a flags) = optionalMask b (flags.map f) := by
  simp only [optionalMask,h.and,ByteAuth.eqMask_map h,OpenResult.get_map h,h.const]
theorem metadata_map (flags raw : List B) :
    (metadata a flags raw).map f = metadata b (flags.map f) (raw.map f) := by
  simp only [metadata,List.map_append,List.map_take,List.map_drop,ByteAuth.release_map h,optionalMask_map h]
theorem construct_map (flags raw : List B) :
    (construct a flags raw).map f = construct b (flags.map f) (raw.map f) := by
  simp only [construct,List.map_append,List.map_cons,List.map_nil,h.and,h.const,
    firstMissing_map h,ByteAuth.eqMask_map h,optionalMask_map h,ByteAuth.release_map h,metadata_map h]
end Refinement

def missingSpec (flags : List (BitVec 8)) : List (Nat × Nat) → BitVec 8
  | [] => 0
  | (i,code) :: rest => if OpenResult.get ByteAuth.concrete flags i = 1 then missingSpec flags rest else BitVec.ofNat 8 code

theorem firstMissing_spec (flags : List (BitVec 8)) (fields : List (Nat × Nat)) :
    firstMissing ByteAuth.concrete flags fields = missingSpec flags fields := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
    rcases field with ⟨i,code⟩
    simp only [firstMissing,ByteAuth.eqMask_value,ih,missingSpec]
    change Unpad.chooseByte ByteAuth.concrete (if OpenResult.get ByteAuth.concrete flags i = 1 then 255 else 0) _ _ = _
    split <;> simp only [Unpad.chooseByte_accept,Unpad.chooseByte_reject]
    rfl

theorem optionalMask_spec (flags : List (BitVec 8)) :
    optionalMask ByteAuth.concrete flags = if OpenResult.get ByteAuth.concrete flags 2 = 1 ∧
      OpenResult.get ByteAuth.concrete flags 3 = 1 then 255 else 0 := by
  simp only [optionalMask,ByteAuth.eqMask_value]
  change (if OpenResult.get ByteAuth.concrete flags 2 = 1 then 255 else 0) &&&
    (if OpenResult.get ByteAuth.concrete flags 3 = 1 then 255 else 0) = _
  by_cases h2 : OpenResult.get ByteAuth.concrete flags 2 = 1 <;>
    by_cases h3 : OpenResult.get ByteAuth.concrete flags 3 = 1 <;>
      simp only [h2,h3,↓reduceIte,and_true,and_false] <;> rfl

theorem metadata_length (a : ByteAuth.Ops B) (flags raw : List B) (h : raw.length = 17) :
    (metadata a flags raw).length = 17 := by simp [metadata,ByteAuth.release,h]
theorem construct_length (a : ByteAuth.Ops B) (flags raw : List B) (h : raw.length = 17) :
    (construct a flags raw).length = 20 := by simp [construct,ByteAuth.release,metadata_length a flags raw h]

theorem compiled_construct_correct (flags raw : List (BVExpr 8)) (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8*(construct ByteAuth.symbolic flags raw).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (construct ByteAuth.symbolic flags raw))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (construct ByteAuth.symbolic flags raw))).vec.get index hi)) =
      (ByteCircuit.joinValue (construct ByteAuth.concrete (flags.map (BVExpr.eval assign)) (raw.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,construct_map (ByteAuth.evaluationHom assign)]
end TlsMpc.Signal.PreKeyBundle
