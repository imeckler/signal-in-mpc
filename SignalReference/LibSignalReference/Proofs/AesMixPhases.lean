import LibSignalReference.Proofs.AesMixPhaseReference
import LibSignalReference.Proofs.AesMixPhaseLayout
import LibSignalReference.Proofs.AesLinear

namespace LibSignalReference.Proofs.AesMixPhases

open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal.AesLayout TlsMpc.Signal.AesRemainingLinear
open LibSignalReference.Proofs.AesLinear
open _root_.Std.Tactic.BVDecide

/-- Public tags 0,1,2 select actual Rust phases 1,2,3. -/
def selected (phase : Fin 3) : Array U64 8#usize → Result (Array U64 8#usize) :=
  match phase.val with
  | 0 => RustCryptoAesRemainingLinear.soft.fixslice.mix_columns_1
  | 1 => RustCryptoAesRemainingLinear.soft.fixslice.mix_columns_2
  | _ => RustCryptoAesRemainingLinear.soft.fixslice.mix_columns_3

theorem selected_reference (words : Words (BitVec 64)) (phase : Fin 3) :
    selected phase (wordArray words) = .ok (wordArray (mixWords (phase.val + 1) words)) := by
  fin_cases phase
  · exact mix1_reference words
  · exact mix2_reference words
  · exact mix3_reference words

theorem selected_network (input : Nat → Nat → BitVec 8) (phase : Fin 3) :
    selected phase (wordArray (network input)) =
      .ok (wordArray (network (phaseBytes Aes.concrete (phase.val + 1) input))) := by
  rw [selected_reference, mixWords_network input ⟨phase.val + 1, by omega⟩]

/-- Each selected actual Rust phase has a numeric circuit expressed through
the existing byte operations, with the proved phase conjugation. All values
of all four input blocks are covered; the public phase and state shape are fixed. -/
theorem mix_phases_refine_artifact (input : Nat → Nat → BitVec 8) (phase : Fin 3)
    (secret : Nat → Nat → BVExpr 8) (assign : BVExpr.Assignment)
    (hsecret : ∀ block index, (secret block index).eval assign = input block index) :
    ∃ result,
      selected phase (wordArray (network input)) = .ok result ∧
      ∀ (index : Nat) (hi : index < 8 * (expr (phase.val + 1) secret).length),
        AigExport.evalRef
          (AigExport.exportNodes (AigExport.compile
            (ByteCircuit.joinExpr (expr (phase.val + 1) secret))).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (AigExport.exportRef ((AigExport.compile
            (ByteCircuit.joinExpr (expr (phase.val + 1) secret))).vec.get index hi)) =
          (ByteCircuit.joinValue (encodeArray result)).getLsbD index := by
  refine ⟨wordArray (network (phaseBytes Aes.concrete (phase.val + 1) input)), selected_network input phase, ?_⟩
  intro index hi
  rw [encode_wordArray, TlsMpc.Signal.AesRemainingLinear.compiled_expr_correct,
    show (fun block index => (secret block index).eval assign) = input from
      funext (fun block => funext (hsecret block)), value_network,
      fast_network input ⟨phase.val + 1, by omega⟩]

end LibSignalReference.Proofs.AesMixPhases
