import Sha256WrapperWork.InitialGenerated.Funs
import LibSignalReference.Proofs.ShaCompact

/-!
Actual pinned sha2 core initialization, plus composition with the already
translated compact compression operation. This file does not assert that the
untranslated block-buffer update/finalize wrappers implement that composition.
-/

namespace LibSignalReference.Candidate.Sha256Wrapper

open Aeneas Aeneas.Std TlsMpc TlsMpc.Sha256
open LibSignalReference.Proofs.Sha256Round
open LibSignalReference.Proofs.ShaCompact
open _root_.Std.Tactic.BVDecide

abbrev newCore :=
  _root_.Sha256Wrapper.block_api.Sha256VarCore.Insts.DigestBlock_apiVariableOutputCoreUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0UIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0EagerUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0TupleUTerm.new

abbrev Core := _root_.Sha256Wrapper.block_api.Sha256VarCore
abbrev makeCore := _root_.Sha256Wrapper.block_api.Sha256VarCore.mk

/-- All accepted and rejected sizes retain the actual implementation result. -/
theorem new_eq (size : Usize) :
    newCore size = .ok (if size.val = 28 then
      .Ok (makeCore _root_.Sha256Wrapper.consts.H256_224 0#u64)
    else if size.val = 32 then
      .Ok (makeCore _root_.Sha256Wrapper.consts.H256_256 0#u64)
    else .Err ()) := by
  unfold newCore
    _root_.Sha256Wrapper.block_api.Sha256VarCore.Insts.DigestBlock_apiVariableOutputCoreUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0UIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0EagerUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0TupleUTerm.new
  split <;> simp_all

theorem new_sha224 : newCore 28#usize =
    .ok (.Ok (makeCore _root_.Sha256Wrapper.consts.H256_224 0#u64)) := by
  rfl

theorem new_sha256 : newCore 32#usize =
    .ok (.Ok (makeCore _root_.Sha256Wrapper.consts.H256_256 0#u64)) := by
  rfl

theorem new_invalid (size : Usize) (h224 : size.val ≠ 28) (h256 : size.val ≠ 32) :
    newCore size = .ok (.Err ()) := by
  simp [new_eq, h224, h256]

/-- This is equality to the circuit's existing initialization, not an assertion
that a separate crypto standard or security property is satisfied. -/
theorem initial_state :
    decodeState _root_.Sha256Wrapper.consts.H256_256 = initial concrete := by
  with_unfolding_all rfl

theorem new_sha256_state :
    ∃ result, newCore 32#usize = .ok (.Ok result) ∧
      decodeState result.state = initial concrete ∧ result.block_len = 0#u64 := by
  exact ⟨_, new_sha256, initial_state, rfl⟩

/-- Constructor followed by the actual selected compression leaf. Inputs here
are sixteen shared words, before the still-unproved byte-loading wrapper. -/
theorem initial_compression (block : Array U32 16#usize) :
    ∃ start result,
      newCore 32#usize = .ok (.Ok start) ∧
      RustCryptoSha256Compact.sha256.soft.compact.compress_u32 start.state block = .ok result ∧
      decodeState result = Signal.ShaCompact.compress concrete (initial concrete) (value block) := by
  refine ⟨makeCore _root_.Sha256Wrapper.consts.H256_256 0#u64,
    encodeState (Signal.ShaCompact.compress concrete (initial concrete) (value block)),
    new_sha256, ?_, ?_⟩
  · simpa only [initial_state] using
      LibSignalReference.Proofs.ShaCompact.compress_all_arrays _root_.Sha256Wrapper.consts.H256_256 block
  · exact decode_encode _

/-- Every numeric MPC output bit equals constructor-plus-compression behavior.
This is deliberately a leaf-composition theorem, not a Digest/update/finalize
wrapper theorem; no opaque buffer or crypto contract is assumed. -/
theorem initial_compression_refines_artifact
    (block : Array U32 16#usize) (secretBlock : List (BVExpr 32))
    (assign : BVExpr.Assignment)
    (hblock : secretBlock.map (BVExpr.eval assign) = value block) :
    ∃ start result,
      newCore 32#usize = .ok (.Ok start) ∧
      RustCryptoSha256Compact.sha256.soft.compact.compress_u32 start.state block = .ok result ∧
      ∀ (index : Nat)
        (hi : index < 8 * (Signal.ShaCompact.bytes symbolic (initial symbolic) secretBlock).length),
        AigExport.evalRef
          (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
            (Signal.ShaCompact.bytes symbolic (initial symbolic) secretBlock))).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
            (Signal.ShaCompact.bytes symbolic (initial symbolic) secretBlock))).vec.get index hi)) =
          (ByteCircuit.joinValue (digest concrete (decodeState result))).getLsbD index := by
  obtain ⟨result, hresult, hbits⟩ :=
    LibSignalReference.Proofs.ShaCompact.compress_refines_artifact
      _root_.Sha256Wrapper.consts.H256_256 block (initial symbolic) secretBlock assign
      (by rw [initial_map (evaluationHom assign), initial_state]) hblock
  exact ⟨makeCore _root_.Sha256Wrapper.consts.H256_256 0#u64, result, new_sha256, hresult, hbits⟩

end LibSignalReference.Candidate.Sha256Wrapper
