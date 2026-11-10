import TlsMpc.Signal.OpenResult

/-! The exact byte preprocessing used by pinned libsignal XEdDSA verification.
This is a necessary check, NEVER signature authentication. In particular the
source accepts s < 2^253 after clearing the sign bit, not only s < ell.
The signature length is public. All byte values and outputs remain shared.
The field arithmetic, SHA512 and their binding must precede authentication. -/
namespace TlsMpc.Signal.XEdDsa
open Std.Tactic.BVDecide

/-- The actual verifier's scalar envelope: original bits 5 and 6 must be zero;
bit 7 carries the sign of the Edwards public key. -/
def scalarMask (a : ByteAuth.Ops B) (last : B) : B :=
  ByteAuth.eqMask a (a.and last (a.const 96)) (a.const 0)

/-- Output envelopeStatus255/0 || sign0/1 || R32 || s32. Invalid public length
returns 66 zeros. Invalid scalar envelope zeros every byte. This status is not
an authentication result; no identity or prekey policy consumes it. -/
def decode (a : ByteAuth.Ops B) (signature : List B) : List B :=
  if signature.length = 64 then
    let last := OpenResult.get a signature 63
    let status := scalarMask a last
    let sign := a.and (a.maskBit last 7) (a.const 1)
    status :: ByteAuth.release a status
      (sign :: signature.take 32 ++ (signature.drop 32).take 31 ++ [a.and last (a.const 127)])
  else List.replicate 66 (a.const 0)

/-- Reconstruct compressed Edwards bytes from *canonical* affine x and y bytes.
Canonical field-to-byte conversion is an explicit external stage obligation. -/
def compress (a : ByteAuth.Ops B) (x y : List B) : List B :=
  y.take 31 ++ [a.xor (a.and (OpenResult.get a y 31) (a.const 127))
    (a.and (a.maskBit (OpenResult.get a x 0) 0) (a.const 128))]

/-- Exact byte comparison at the verifier's final boundary. Caller must bind
candidate coordinates to the computed double-scalar result and validated A.
It does not take a trusted Boolean authentication flag. -/
def matchR (a : ByteAuth.Ops B) (signature x y : List B) : B :=
  if signature.length = 64 ∧ x.length = 32 ∧ y.length = 32 then
    a.and (scalarMask a (OpenResult.get a signature 63))
      (ByteAuth.equalMask a (signature.take 32) (compress a x y))
  else a.const 0

section Refinement
variable {a : ByteAuth.Ops B} {b : ByteAuth.Ops B'} {f : B → B'} (h : ByteAuth.Hom a b f)
include h

theorem scalarMask_map (last : B) : f (scalarMask a last) = scalarMask b (f last) := by
  simp only [scalarMask,ByteAuth.eqMask_map h,h.and,h.const]
theorem decode_map (signature : List B) :
    (decode a signature).map f = decode b (signature.map f) := by
  simp only [decode,List.length_map]
  split <;> simp only [List.map_cons,scalarMask_map h,OpenResult.get_map h,
    ByteAuth.release_map h,List.map_append,List.map_take,List.map_drop,List.map_nil,
    h.and,h.maskBit,h.const,List.map_replicate]
theorem compress_map (x y : List B) :
    (compress a x y).map f = compress b (x.map f) (y.map f) := by
  simp only [compress,List.map_append,List.map_take,List.map_cons,List.map_nil,
    h.xor,h.and,h.const,h.maskBit,OpenResult.get_map h]
theorem matchR_map (signature x y : List B) :
    f (matchR a signature x y) = matchR b (signature.map f) (x.map f) (y.map f) := by
  simp only [matchR,List.length_map]
  split <;> simp only [h.and,h.const,scalarMask_map h,OpenResult.get_map h,
    ByteAuth.equalMask_map h,List.map_take,compress_map h]
end Refinement

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem scalarMask_spec (last : BitVec 8) :
    scalarMask ByteAuth.concrete last = if (last &&& 127).toNat < 32 then 255 else 0 := by
  have all : ∀ last : BitVec 8,
      scalarMask ByteAuth.concrete last = if (last &&& 127).toNat < 32 then 255 else 0 := by decide +kernel
  exact all last

theorem decode_length (a : ByteAuth.Ops B) (signature : List B) : (decode a signature).length = 66 := by
  unfold decode
  split <;> simp_all [ByteAuth.release]

theorem compiled_decode_correct (signature : List (BVExpr 8)) (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8*(decode ByteAuth.symbolic signature).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (decode ByteAuth.symbolic signature))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (decode ByteAuth.symbolic signature))).vec.get index hi)) =
      (ByteCircuit.joinValue (decode ByteAuth.concrete (signature.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,decode_map (ByteAuth.evaluationHom assign)]

theorem compiled_matchR_correct (signature x y : List (BVExpr 8)) (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8*([matchR ByteAuth.symbolic signature x y]).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr [matchR ByteAuth.symbolic signature x y])).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr [matchR ByteAuth.symbolic signature x y])).vec.get index hi)) =
      (ByteCircuit.joinValue [matchR ByteAuth.concrete (signature.map (BVExpr.eval assign))
        (x.map (BVExpr.eval assign)) (y.map (BVExpr.eval assign))]).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct]
  simp only [List.map_cons,List.map_nil]
  rw [matchR_map (ByteAuth.evaluationHom assign) signature x y]
end TlsMpc.Signal.XEdDsa
