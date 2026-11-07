import LibSignalReference.Proofs.AesLinearProofs
import LibSignalReference.Proofs.AesLayout

namespace LibSignalReference.Proofs.AesLinear

open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal.AesLayout TlsMpc.Signal.AesLinear
open _root_.Std.Tactic.BVDecide

def encodeArray (result : Array U64 8#usize) : List (BitVec 8) :=
  result.val.flatMap (fun word => (List.range 8).map (fun offset => word.bv.extractLsb' (offset * 8) 8))

theorem encode_wordArray (words : Words (BitVec 64)) :
    encodeArray (wordArray words) = encodeWords words := by rfl

theorem mix_network (input : Nat → Nat → BitVec 8) :
    RustCryptoAesLinear.soft.fixslice.mix_columns_0 (wordArray (network input)) =
      .ok (wordArray (network (mixBytes Aes.concrete input))) := by
  rw [mix_reference, mixWords_network]

/-- Four secret sixteen-byte blocks enter the ordinary bitplane layout.
The numeric circuit implements the selected actual Rust phase-zero MixColumns,
including the existing root byte operation. The public shape excludes no byte
values; all output bitplanes remain secret. -/
theorem mix_refines_artifact (input : Nat → Nat → BitVec 8)
    (secret : Nat → Nat → BVExpr 8) (assign : BVExpr.Assignment)
    (hsecret : ∀ block index, (secret block index).eval assign = input block index) :
    ∃ result,
      RustCryptoAesLinear.soft.fixslice.mix_columns_0 (wordArray (network input)) = .ok result ∧
      ∀ (index : Nat) (hi : index < 8 * (TlsMpc.Signal.AesLinear.expr secret).length),
        AigExport.evalRef
          (AigExport.exportNodes (AigExport.compile
            (ByteCircuit.joinExpr (TlsMpc.Signal.AesLinear.expr secret))).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (AigExport.exportRef ((AigExport.compile
            (ByteCircuit.joinExpr (TlsMpc.Signal.AesLinear.expr secret))).vec.get index hi)) =
          (ByteCircuit.joinValue (encodeArray result)).getLsbD index := by
  refine ⟨wordArray (network (mixBytes Aes.concrete input)), mix_network input, ?_⟩
  intro index hi
  rw [encode_wordArray, TlsMpc.Signal.AesLinear.compiled_expr_correct,
    show (fun block index => (secret block index).eval assign) = input from
      funext (fun block => funext (hsecret block)), value_network]

end LibSignalReference.Proofs.AesLinear
