import TlsMpc.Signal.OpenResult

/-! Typed prekey input leaves, matching pinned core PublicKey and protocol KEM
public-key deserialization. EC keys allow trailing bytes; KEM keys do not.
Feature availability and byte lengths are public; values and errors stay shared.
Error codes0=success,1=no tag,2=bad tag,3=bad length normalize Rust error classes.
This does not specify a combined wire-parser order: PreKeyBundleContent already
contains typed keys, and its constructor performs no key deserialization. -/
namespace TlsMpc.Signal.PreKeyWire
open Std.Tactic.BVDecide

structure Features where
  kyber768 : Bool := false
  mlkem1024 : Bool := false
  deriving DecidableEq

def bor (a : ByteAuth.Ops B) (x y : B) : B := a.xor (a.xor x y) (a.and x y)

def ecCode (a : ByteAuth.Ops B) (raw : List B) : B :=
  if raw.length = 0 then a.const 1 else
    Unpad.chooseByte a (ByteAuth.eqMask a (OpenResult.get a raw 0) (a.const 5))
      (a.const (if 33 ≤ raw.length then 0 else 3)) (a.const 2)

/-- status255/0 || errorCode || canonical tag5+raw32. Every payload byte is
zero on failure. Trailing EC bytes are ignored exactly as by deserialize/serialize. -/
def ec (a : ByteAuth.Ops B) (raw : List B) : List B :=
  let code := ecCode a raw
  let ok := ByteAuth.eqMask a code (a.const 0)
  [ok,code] ++ ByteAuth.release a ok (a.const 5 :: (List.range 32).map (fun i => OpenResult.get a raw (i+1)))

def kemTag (a : ByteAuth.Ops B) (features : Features) (tag : B) : B :=
  bor a (ByteAuth.eqMask a tag (a.const 8))
    (bor a (if features.kyber768 then ByteAuth.eqMask a tag (a.const 7) else a.const 0)
      (if features.mlkem1024 then ByteAuth.eqMask a tag (a.const 10) else a.const 0))

def kemCode (a : ByteAuth.Ops B) (features : Features) (raw : List B) : B :=
  if raw.length = 0 then a.const 1 else
    let tag := OpenResult.get a raw 0
    let lengthOK := Unpad.chooseByte a (ByteAuth.eqMask a tag (a.const 7))
      (a.const (if raw.length = 1185 then 255 else 0))
      (a.const (if raw.length = 1569 then 255 else 0))
    Unpad.chooseByte a (kemTag a features tag)
      (Unpad.chooseByte a lengthOK (a.const 0) (a.const 3)) (a.const 2)

/-- status || code || exact typed KEM wire. The whole raw wire is the signature
message on success, including its algorithm tag. No coefficient check is added. -/
def kem (a : ByteAuth.Ops B) (features : Features) (raw : List B) : List B :=
  let code := kemCode a features raw
  let ok := ByteAuth.eqMask a code (a.const 0)
  [ok,code] ++ ByteAuth.release a ok raw

/-- DeviceId::try_from(u32), using four-byte big-endian input. Its accepted
range is1..127. Registration/prekey IDs are unrestricted u32 and are not narrowed. -/
def device (a : ByteAuth.Ops B) (raw : List B) : List B :=
  let last := OpenResult.get a raw 3
  let ok := if raw.length = 4 then
    a.and (ByteAuth.equalMask a (raw.take 3) (List.replicate 3 (a.const 0)))
      (a.and (a.not (ByteAuth.eqMask a last (a.const 0))) (a.not (a.maskBit last 7)))
    else a.const 0
  [ok,a.and ok last]

section Refinement
variable {a : ByteAuth.Ops B} {b : ByteAuth.Ops B'} {f : B → B'} (h : ByteAuth.Hom a b f)
include h

theorem bor_map (x y : B) : f (bor a x y) = bor b (f x) (f y) := by simp only [bor,h.xor,h.and]
theorem ecCode_map (raw : List B) : f (ecCode a raw) = ecCode b (raw.map f) := by
  simp only [ecCode,List.length_map]; split <;> simp only [h.const,Unpad.chooseByte_map h,ByteAuth.eqMask_map h,OpenResult.get_map h]
theorem ec_map (raw : List B) : (ec a raw).map f = ec b (raw.map f) := by
  simp only [ec,List.map_append,List.map_cons,List.map_nil,ByteAuth.release_map h,
    ByteAuth.eqMask_map h,ecCode_map h,h.const,List.map_map,Function.comp_def,OpenResult.get_map h]
theorem kemTag_map (features : Features) (tag : B) : f (kemTag a features tag) = kemTag b features (f tag) := by
  cases features with
  | mk k m => cases k <;> cases m <;> simp only [kemTag,bor_map h,ByteAuth.eqMask_map h,h.const,↓reduceIte,Bool.false_eq_true]
theorem kemCode_map (features : Features) (raw : List B) : f (kemCode a features raw) = kemCode b features (raw.map f) := by
  simp only [kemCode,List.length_map]; split <;> simp only [h.const,Unpad.chooseByte_map h,
    ByteAuth.eqMask_map h,OpenResult.get_map h,kemTag_map h]
theorem kem_map (features : Features) (raw : List B) : (kem a features raw).map f = kem b features (raw.map f) := by
  simp only [kem,List.map_append,List.map_cons,List.map_nil,ByteAuth.release_map h,
    ByteAuth.eqMask_map h,kemCode_map h,h.const]
theorem device_map (raw : List B) : (device a raw).map f = device b (raw.map f) := by
  simp only [device,List.length_map]; split <;> simp only [List.map_cons,List.map_nil,h.and,h.const,h.not,h.maskBit,
    ByteAuth.eqMask_map h,ByteAuth.equalMask_map h,List.map_take,List.map_replicate,OpenResult.get_map h]
end Refinement

def ecSpecCode (raw : List (BitVec 8)) : BitVec 8 :=
  if raw.length = 0 then 1 else if OpenResult.get ByteAuth.concrete raw 0 = 5 then
    if 33 ≤ raw.length then 0 else 3 else 2

theorem ecCode_spec (raw : List (BitVec 8)) : ecCode ByteAuth.concrete raw = ecSpecCode raw := by
  unfold ecCode ecSpecCode
  split <;> first | rfl | skip
  rw [ByteAuth.eqMask_value]
  change (Unpad.chooseByte ByteAuth.concrete (if OpenResult.get ByteAuth.concrete raw 0 = 5 then 255 else 0) _ _) = _
  by_cases ht : OpenResult.get ByteAuth.concrete raw 0 = 5
  · simp only [ht,↓reduceIte,Unpad.chooseByte_accept]
    split <;> rfl
  · simp only [ht,↓reduceIte,Unpad.chooseByte_reject]
    rfl

/-- An absent optional typed key has no raw bytes to validate. This gate keeps
its dummy fixed-profile slot from adding a new policy to Option::None. -/
def optionalStatus (a : ByteAuth.Ops B) (flag decodedStatus : B) : B :=
  Unpad.chooseByte a (ByteAuth.eqMask a flag (a.const 1)) decodedStatus (a.const 255)
theorem optionalStatus_map {a : ByteAuth.Ops B} {b : ByteAuth.Ops B'} {f : B → B'}
    (h : ByteAuth.Hom a b f) (flag decodedStatus : B) :
    f (optionalStatus a flag decodedStatus) = optionalStatus b (f flag) (f decodedStatus) := by
  simp only [optionalStatus,Unpad.chooseByte_map h,ByteAuth.eqMask_map h,h.const]

def run (a : ByteAuth.Ops B) (features : Features) (mode : Nat) (raw : List B) : List B :=
  if mode = 0 then ec a raw else if mode = 1 then kem a features raw else if mode = 2 then device a raw
  else [optionalStatus a (OpenResult.get a raw 0) (OpenResult.get a raw 1)]

theorem run_map {a : ByteAuth.Ops B} {b : ByteAuth.Ops B'} {f : B → B'}
    (h : ByteAuth.Hom a b f) (features : Features) (mode : Nat) (raw : List B) :
    (run a features mode raw).map f = run b features mode (raw.map f) := by
  unfold run; split <;> first | exact ec_map h raw | skip
  split
  · exact kem_map h features raw
  · split
    · exact device_map h raw
    · simp only [List.map_cons,List.map_nil,optionalStatus_map h,OpenResult.get_map h]

theorem compiled_run_correct (features : Features) (mode : Nat) (raw : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8*(run ByteAuth.symbolic features mode raw).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (run ByteAuth.symbolic features mode raw))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (run ByteAuth.symbolic features mode raw))).vec.get index hi)) =
      (ByteCircuit.joinValue (run ByteAuth.concrete features mode (raw.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,run_map (ByteAuth.evaluationHom assign)]
end TlsMpc.Signal.PreKeyWire
