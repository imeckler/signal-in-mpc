import LibSignalReference.Proofs.AesLayoutReference
import LibSignalReference.Proofs.AesLayoutPermutation
import TlsMpc.Signal.AesLayout

namespace TlsMpc.Signal.AesLayout

set_option maxHeartbeats 4000000

theorem byteValue_bit (input : Nat → Nat → BitVec 8) (plane offset : Nat) (bit : Fin 8) :
    (byteValue input plane offset).getLsbD bit.val =
      (input (sourceBlock (offset * 8 + bit.val))
        (sourceByte (offset * 8 + bit.val))).getLsbD plane := by
  fin_cases bit <;>
    simp only [byteValue, AesSbox.packValue, BitVec.getLsbD_append] <;> simp

theorem byteValue_network (input : Nat → Nat → BitVec 8) (plane offset : Fin 8) :
    byteValue input plane.val offset.val =
      ((network input).at plane.val).extractLsb' (offset.val * 8) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit
  by_cases hb : bit < 8
  · rw [byteValue_bit input plane.val offset.val ⟨bit,hb⟩,
      BitVec.getLsbD_extractLsb']
    simp only [hb, decide_true, Bool.true_and, true_implies]
    exact (network_bit input plane ⟨offset.val * 8 + bit, by omega⟩).symm
  · simp [hb]

theorem value_network (input : Nat → Nat → BitVec 8) :
    value input = encodeWords (network input) := by
  apply List.map_congr_left
  intro index hindex
  have hi : index < 64 := List.mem_range.mp hindex
  exact byteValue_network input ⟨index / 8, by omega⟩ ⟨index % 8, by omega⟩

end TlsMpc.Signal.AesLayout

namespace LibSignalReference.Proofs.AesLayout

open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal.AesLayout
open _root_.Std.Tactic.BVDecide

def encodeResult (result : Slice U64) : List (BitVec 8) :=
  result.val.flatMap (fun word => (List.range 8).map (fun offset => word.bv.extractLsb' (offset * 8) 8))

theorem encode_wordSlice (words : Words (BitVec 64)) :
    encodeResult (wordSlice words) = encodeWords words := by rfl

/-- A complete numeric-artifact refinement of the selected actual Rust function.
The output remains secret and is encoded as eight little-endian bitplanes.
The public domain is four input slices of exactly sixteen bytes and an output
slice of exactly eight u64 words. -/
theorem bitslice_refines_artifact (input : Nat → Nat → U8) (initial : Words (BitVec 64))
    (secret : Nat → Nat → BVExpr 8) (assign : BVExpr.Assignment)
    (hsecret : ∀ block index, (secret block index).eval assign = (input block index).bv) :
    ∃ result,
      RustCryptoAesLayout.soft.fixslice.bitslice (wordSlice initial)
        (slice16 (input 0)) (slice16 (input 1)) (slice16 (input 2)) (slice16 (input 3)) = .ok result ∧
      ∀ (index : Nat) (hi : index < 8 * (expr secret).length),
        AigExport.evalRef
          (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (expr secret))).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (expr secret))).vec.get index hi)) =
          (ByteCircuit.joinValue (encodeResult result)).getLsbD index := by
  refine ⟨wordSlice (network (fun block index => (input block index).bv)), bitslice_network input initial, ?_⟩
  intro index hi
  rw [encode_wordSlice, compiled_expr_correct, show (fun block index => (secret block index).eval assign) =
    (fun block index => (input block index).bv) from funext (fun block => funext (hsecret block)), value_network]

end LibSignalReference.Proofs.AesLayout
