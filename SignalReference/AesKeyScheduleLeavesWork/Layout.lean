import AesKeyScheduleLeavesWork.Equalities
import LibSignalReference.Proofs.AesLayout

namespace LibSignalReference.Proofs.AesKeyScheduleLeaves

open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal.AesLayout
open LibSignalReference.Proofs.AesLayout
open _root_.Std.Tactic.BVDecide

theorem read_reference (input : Nat → U8) :
    RustCryptoAesKeySchedule.soft.fixslice.bitslice.read_reordered (slice12 input) =
      .ok ⟨readReordered (fun i => (input i).bv)⟩ := by
  rw [read_reordered_eq]
  exact read_refines input

theorem delta2_reference (a b mask : U64) (shift : U32) (hshift : shift.val < 64) :
    RustCryptoAesKeySchedule.soft.fixslice.delta_swap_2 a b shift mask =
      .ok (⟨(deltaSwap a.bv b.bv shift.val mask.bv).1⟩,
        ⟨(deltaSwap a.bv b.bv shift.val mask.bv).2⟩) := by
  rw [delta_swap2_eq]
  exact delta_refines a b mask shift hshift

theorem bitslice_reference (input : Nat → Nat → U8) (initial : Words (BitVec 64)) :
    RustCryptoAesKeySchedule.soft.fixslice.bitslice (wordSlice initial)
      (slice16 (input 0)) (slice16 (input 1)) (slice16 (input 2)) (slice16 (input 3)) =
      .ok (wordSlice (network (fun block byte => (input block byte).bv))) := by
  rw [bitslice_eq]
  exact bitslice_network input initial

theorem bitslice_refines_artifact (input : Nat → Nat → U8) (initial : Words (BitVec 64))
    (secret : Nat → Nat → BVExpr 8) (assign : BVExpr.Assignment)
    (hsecret : ∀ block byte, (secret block byte).eval assign = (input block byte).bv) :
    ∃ result,
      RustCryptoAesKeySchedule.soft.fixslice.bitslice (wordSlice initial)
        (slice16 (input 0)) (slice16 (input 1)) (slice16 (input 2)) (slice16 (input 3)) = .ok result ∧
      ∀ (index : Nat) (hi : index < 8 * (expr secret).length),
        AigExport.evalRef
          (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (expr secret))).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (expr secret))).vec.get index hi)) =
          (ByteCircuit.joinValue (encodeResult result)).getLsbD index := by
  rw [bitslice_eq]
  exact AesLayout.bitslice_refines_artifact input initial secret assign hsecret

end LibSignalReference.Proofs.AesKeyScheduleLeaves
