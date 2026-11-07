import LibSignalReference.Proofs.AesShiftBits
import LibSignalReference.Proofs.AesLayout

namespace LibSignalReference.Proofs.AesLinear

open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal.AesLayout TlsMpc.Signal.AesLinear
open LibSignalReference.Proofs.AesLayout
open _root_.Std.Tactic.BVDecide

theorem shift_network (input : Nat → Nat → BitVec 8) :
    RustCryptoAesLinear.soft.fixslice.shift_rows_1 (wordSlice (network input)) =
      .ok (wordSlice (network (shiftBytes Aes.concrete input))) := by
  rw [shift1_reference, shift1_network]

/-- On the public eight-word shape, the selected actual Rust ShiftRows1
and the existing root byte permutation produce the same secret output. -/
theorem shift_refines_artifact (input : Nat → Nat → BitVec 8)
    (secret : Nat → Nat → BVExpr 8) (assign : BVExpr.Assignment)
    (hsecret : ∀ block index, (secret block index).eval assign = input block index) :
    ∃ result,
      RustCryptoAesLinear.soft.fixslice.shift_rows_1 (wordSlice (network input)) = .ok result ∧
      ∀ (index : Nat) (hi : index < 8 * (shiftExpr secret).length),
        AigExport.evalRef
          (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (shiftExpr secret))).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (shiftExpr secret))).vec.get index hi)) =
          (ByteCircuit.joinValue (encodeResult result)).getLsbD index := by
  refine ⟨wordSlice (network (shiftBytes Aes.concrete input)), shift_network input, ?_⟩
  intro index hi
  rw [encode_wordSlice, compiled_shiftExpr_correct,
    show (fun block index => (secret block index).eval assign) = input from
      funext (fun block => funext (hsecret block)), value_network]

theorem shift2_reference_network (input : Nat → Nat → BitVec 8) :
    RustCryptoAesLinear.soft.fixslice.shift_rows_2 (wordSlice (network input)) =
      .ok (wordSlice (network (shiftBytesN Aes.concrete 2 input))) := by
  rw [shift2_reference, shift2_network]

theorem shift3_reference_network (input : Nat → Nat → BitVec 8) :
    RustCryptoAesLinear.soft.fixslice.shift_rows_3 (wordSlice (network input)) =
      .ok (wordSlice (network (shiftBytesN Aes.concrete 3 input))) := by
  rw [shift3_reference, shift3_network]

theorem shift2_refines_artifact (input : Nat → Nat → BitVec 8)
    (secret : Nat → Nat → BVExpr 8) (assign : BVExpr.Assignment)
    (hsecret : ∀ block index, (secret block index).eval assign = input block index) :
    ∃ result,
      RustCryptoAesLinear.soft.fixslice.shift_rows_2 (wordSlice (network input)) = .ok result ∧
      ∀ (index : Nat) (hi : index < 8 * (shiftNExpr 2 secret).length),
        AigExport.evalRef
          (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (shiftNExpr 2 secret))).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (shiftNExpr 2 secret))).vec.get index hi)) =
          (ByteCircuit.joinValue (encodeResult result)).getLsbD index := by
  refine ⟨wordSlice (network (shiftBytesN Aes.concrete 2 input)), shift2_reference_network input, ?_⟩
  intro index hi
  rw [encode_wordSlice, compiled_shiftNExpr_correct,
    show (fun block index => (secret block index).eval assign) = input from
      funext (fun block => funext (hsecret block)), value_network]

theorem shift3_refines_artifact (input : Nat → Nat → BitVec 8)
    (secret : Nat → Nat → BVExpr 8) (assign : BVExpr.Assignment)
    (hsecret : ∀ block index, (secret block index).eval assign = input block index) :
    ∃ result,
      RustCryptoAesLinear.soft.fixslice.shift_rows_3 (wordSlice (network input)) = .ok result ∧
      ∀ (index : Nat) (hi : index < 8 * (shiftNExpr 3 secret).length),
        AigExport.evalRef
          (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (shiftNExpr 3 secret))).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (shiftNExpr 3 secret))).vec.get index hi)) =
          (ByteCircuit.joinValue (encodeResult result)).getLsbD index := by
  refine ⟨wordSlice (network (shiftBytesN Aes.concrete 3 input)), shift3_reference_network input, ?_⟩
  intro index hi
  rw [encode_wordSlice, compiled_shiftNExpr_correct,
    show (fun block index => (secret block index).eval assign) = input from
      funext (fun block => funext (hsecret block)), value_network]

end LibSignalReference.Proofs.AesLinear
