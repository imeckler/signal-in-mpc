import TlsMpc.Signal.ChainSend
import TlsMpc.X25519

/-! Signal RootKey::create_chain composition. X25519 uses the existing field
circuit; its canonical shared 32-byte result enters this Boolean HKDF circuit.
All-zero agreement rejects, preserving the old root and zeroing the new chain.
The accepted output is a new root, a new chain and counter zero. Neither curve
inputs, agreement nor outputs are revealed by this module.

The composition theorem states the exact field/byte representation boundary.
The MPC conversion implementation, faithful actual dalek/RustCrypto reference
equivalence, complete DH-ratchet state policy and atomic commit remain separate.
This module does not generate the new private key or verify identity signatures. -/

namespace TlsMpc.Signal.DhRatchet
open Std.Tactic.BVDecide

def material (s : Sha256.Ops B W) (root agreement : List B) : List B :=
  TlsKdf.expandCore s (TlsKdf.extract s root agreement)
    ((TlsKdf.ascii "WhisperRatchet").map s.byteConst) 64

def materialFast (s : Sha256.Ops B W) (root agreement : List B) : List B :=
  TlsKdf.expandFast s (TlsKdf.extract s root agreement)
    ((TlsKdf.ascii "WhisperRatchet").map s.byteConst) 64

theorem materialFast_correct (s : Sha256.Ops B W) (root agreement : List B) :
    materialFast s root agreement = material s root agreement := by
  simp only [materialFast, material, TlsKdf.expandFast_correct]

theorem material_length (s : Sha256.Ops B W) (root agreement : List B) :
    (material s root agreement).length = 64 := by
  simp [material, TlsKdf.expandCore_length]

def agreementMask (a : ByteAuth.Ops B) (agreement : List B) : B :=
  a.not (ByteAuth.equalMask a agreement (List.replicate 32 (a.const 0)))

/-- Shared status, root32, chain32, new counterBE4. On rejection the old root
is retained and the chain/counter outputs are zero. -/
def createCore (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (root agreement : List B) : List B :=
  let accepted := agreementMask a agreement
  let output := materialFast s root agreement
  accepted :: (ChainSend.selectState a accepted (output.take 32) root ++
    ByteAuth.release a accepted (output.drop 32) ++ List.replicate 4 (a.const 0))

def createChecked (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (root agreement : List B) : Option (List B) :=
  if root.length = 32 ∧ agreement.length = 32 then some (createCore s a root agreement) else none

section Refinement
variable {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {fw : W → W'} (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)
include hs

theorem material_map (root agreement : List B) :
    (material s root agreement).map f = material s' (root.map f) (agreement.map f) := by
  simp only [material, TlsKdf.expandCore_map hs, TlsKdf.extract_map hs,
    List.map_map, Function.comp_def, hs.byteConst]

theorem materialFast_map (root agreement : List B) :
    (materialFast s root agreement).map f = materialFast s' (root.map f) (agreement.map f) := by
  rw [materialFast_correct, materialFast_correct, material_map hs]

omit hs in
include ha in
theorem agreementMask_map (agreement : List B) :
    f (agreementMask a agreement) = agreementMask a' (agreement.map f) := by
  simp only [agreementMask, ha.not, ByteAuth.equalMask_map ha, List.map_replicate, ha.const]

include ha

theorem createCore_map (root agreement : List B) :
    (createCore s a root agreement).map f = createCore s' a' (root.map f) (agreement.map f) := by
  simp only [createCore, List.map_cons, List.map_append, ChainSend.selectState_map ha,
    ByteAuth.release_map ha, agreementMask_map ha, materialFast_map hs,
    List.map_take, List.map_drop, List.map_replicate, ha.const]

theorem createChecked_map (root agreement : List B) :
    (createChecked s a root agreement).map (List.map f) = createChecked s' a' (root.map f) (agreement.map f) := by
  simp only [createChecked, List.length_map]
  split <;> simp [createCore_map hs ha]

end Refinement

theorem agreementMask_value (agreement : List (BitVec 8)) :
    agreementMask ByteAuth.concrete agreement = if agreement ≠ List.replicate 32 0 then 255 else 0 := by
  simp only [agreementMask, ByteAuth.equalMask_value]
  change (~~~(if agreement = List.replicate 32 0 then 255 else 0)) = _
  split <;> simp_all

def spec (root agreement : List (BitVec 8)) : List (BitVec 8) :=
  let output := material Sha256.concrete root agreement
  if agreement = List.replicate 32 0 then 0 :: (root ++ List.replicate 36 0)
  else 255 :: (output.take 32 ++ output.drop 32 ++ List.replicate 4 0)

theorem createCore_concrete_correct (root agreement : List (BitVec 8)) (hroot : root.length = 32) :
    createCore Sha256.concrete ByteAuth.concrete root agreement = spec root agreement := by
  have hk : ((material Sha256.concrete root agreement).take 32).length = root.length := by
    simp [material_length, hroot]
  have hm : ((material Sha256.concrete root agreement).drop 32).length = 32 := by
    simp [material_length]
  simp only [createCore, materialFast_correct, agreementMask_value]
  split
  · rename_i good
    rw [ChainSend.selectState_accept _ _ hk, ByteAuth.release_accept]
    simp only [spec, if_neg good]
    rfl
  · rename_i bad
    rw [ChainSend.selectState_reject, ByteAuth.release_reject, hm]
    simp only [spec, if_pos (Classical.not_not.mp bad)]
    change 0 :: ((root ++ List.replicate 32 0) ++ List.replicate 4 0) = _
    rw [List.append_assoc, List.replicate_append_replicate]

theorem zero_agreement_preserves_root (root : List (BitVec 8)) :
    createCore Sha256.concrete ByteAuth.concrete root (List.replicate 32 0) =
      0 :: (root ++ List.replicate 36 0) := by
  have hm : agreementMask ByteAuth.concrete (List.replicate 32 0) = 0 := by
    simp [agreementMask_value]
  simp only [createCore, hm, ChainSend.selectState_reject,
    ByteAuth.release_reject, materialFast_correct, List.length_drop, material_length]
  change 0 :: ((root ++ List.replicate 32 0) ++ List.replicate 4 0) = _
  rw [List.append_assoc, List.replicate_append_replicate]

theorem createCore_length (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (root agreement : List B) :
    (createCore s a root agreement).length = 1 + root.length + 36 := by
  simp [createCore, ChainSend.selectState, ByteAuth.release, materialFast_correct, material_length]
  omega

theorem compiled_createCore_correct (root agreement : List (BVExpr 8))
    (assign : BVExpr.Assignment) (bit : Nat)
    (hi : bit < 8 * (createCore Sha256.symbolic ByteAuth.symbolic root agreement).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (createCore Sha256.symbolic ByteAuth.symbolic root agreement))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (createCore Sha256.symbolic ByteAuth.symbolic root agreement))).vec.get bit hi)) =
      (ByteCircuit.joinValue (createCore Sha256.concrete ByteAuth.concrete
        (root.map (BVExpr.eval assign)) (agreement.map (BVExpr.eval assign)))).getLsbD bit := by
  rw [ByteCircuit.compile_bytes_correct, createCore_map (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]

theorem compiled_createCore_spec (root agreement : List (BVExpr 8)) (hroot : root.length = 32)
    (assign : BVExpr.Assignment) (bit : Nat)
    (hi : bit < 8 * (createCore Sha256.symbolic ByteAuth.symbolic root agreement).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (createCore Sha256.symbolic ByteAuth.symbolic root agreement))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (createCore Sha256.symbolic ByteAuth.symbolic root agreement))).vec.get bit hi)) =
      (ByteCircuit.joinValue (spec (root.map (BVExpr.eval assign)) (agreement.map (BVExpr.eval assign)))).getLsbD bit := by
  rw [compiled_createCore_correct, createCore_concrete_correct _ _ (by simpa using hroot)]

def fieldBytes (value : FieldDag.F) : List (BitVec 8) :=
  (X25519.encode value).map (fun byte => BitVec.ofNat 8 byte.toNat)

theorem fieldBytes_length (value : FieldDag.F) : (fieldBytes value).length = 32 := by
  simp [fieldBytes, X25519.encode]

def operationSpec (root : List (BitVec 8)) (scalar : Nat → Bool) (point : FieldDag.F) : List (BitVec 8) :=
  spec root (fieldBytes (X25519.spec scalar point))

/-- Composition of both proved numeric circuits, conditional only on the exact
shared field-to-byte representation relation. This is not a security proof of
the unverified conversion protocol and not yet actual libsignal equivalence. -/
theorem compiled_composition_correct
    (scalar : Nat → Bool) (point : FieldDag.F) (fieldArtifact : FieldDag.Artifact)
    (compiled : FieldDag.compile X25519.expr = some fieldArtifact)
    (root agreement : List (BVExpr 8)) (hroot : root.length = 32) (assign : BVExpr.Assignment)
    (conversion : agreement.map (BVExpr.eval assign) = fieldBytes
      (FieldDag.result (FieldDag.concrete (X25519.assignment scalar point)) fieldArtifact.nodes fieldArtifact.output))
    (bit : Nat) (hi : bit < 8 * (createCore Sha256.symbolic ByteAuth.symbolic root agreement).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (createCore Sha256.symbolic ByteAuth.symbolic root agreement))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (createCore Sha256.symbolic ByteAuth.symbolic root agreement))).vec.get bit hi)) =
      (ByteCircuit.joinValue (operationSpec (root.map (BVExpr.eval assign)) scalar point)).getLsbD bit := by
  rw [compiled_createCore_spec root agreement hroot, conversion,
    X25519.compiled_compute_correct scalar point fieldArtifact compiled]
  rfl

end TlsMpc.Signal.DhRatchet
