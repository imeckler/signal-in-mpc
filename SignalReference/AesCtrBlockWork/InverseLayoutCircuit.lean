import AesCtrBlockWork.FactoredInverse
import LibSignalReference.Proofs.AesLayoutPermutation
namespace LibSignalReference.Candidate.AesInverseCircuit
open Aeneas Aeneas.Std TlsMpc.Signal.AesLayout
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

theorem words_ext (a b : Words W) (h : ∀ p : Fin 8, a.at p.val=b.at p.val) : a=b := by
 cases a; cases b
 simp only [Words.mk.injEq]
 exact ⟨h 0,h 1,h 2,h 3,h 4,h 5,h 6,h 7⟩

theorem transpose_involution (words : Words (BitVec 64)) :
 transpose (transpose words) = words := by
 apply words_ext
 intro plane
 apply BitVec.eq_of_getLsbD_eq
 intro lane hl
 rw [transpose_bit _ plane ⟨lane,hl⟩,
     transpose_bit _ ⟨lane%8,by omega⟩ ⟨lane/8*8+plane.val,by omega⟩]
 dsimp only
 congr 2 <;> omega

open LibSignalReference.Candidate.AesCtrInverse
open LibSignalReference.Proofs.AesLayout
open LibSignalReference.Candidate.AesInverseComposition

theorem write_read_bytes (input : Nat→BitVec 8) :
 blockBytes (readReordered input) (readReordered (fun n=>input (n+4))) =
 [input 0,input 1,input 2,input 3,input 4,input 5,input 6,input 7,
  input 8,input 9,input 10,input 11,input 12,input 13,input 14,input 15] := by
 simp only [blockBytes, List.cons.injEq]
 repeat' apply And.intro
 all_goals first | trivial | skip
 all_goals
  apply BitVec.eq_of_getLsbD_eq
  intro bit hb
  interval_cases bit <;> simp [readReordered]

def originalBatch (input : Nat→Nat→BitVec 8) :
 RustCryptoAesCtrInverse.hybrid_array.Array.specialized_Type_466e03121b73c7d435361c7adc904649fbf81c760e593c61b65a8532a101fdf5 :=
 ⟨(List.range 4).map (fun block=>⟨((List.range 16).map (fun byte=>(⟨input block byte⟩ : U8))),by simp⟩),by simp⟩

theorem inverse_network (input : Nat→Nat→BitVec 8) :
 inverseResult (network input) = originalBatch input := by
 simp only [inverseResult, network, transpose_involution, prepare, blockArray, write_read_bytes]
 with_unfolding_all rfl

theorem actual_inverse_network (input : Nat→Nat→BitVec 8) :
 RustCryptoAesCtrInverse.soft.fixslice.inv_bitslice (wordSlice (network input)) =
 .ok (originalBatch input) := by
 rw [actual_inverse, inverse_network]

theorem actual_bitslice_inverse (input : Nat→Nat→U8) (initial : Words (BitVec 64)) :
 (do
   let encoded←RustCryptoAesLayout.soft.fixslice.bitslice (wordSlice initial)
     (slice16 (input 0)) (slice16 (input 1)) (slice16 (input 2)) (slice16 (input 3))
   RustCryptoAesCtrInverse.soft.fixslice.inv_bitslice encoded) =
 .ok (originalBatch (fun block byte=>(input block byte).bv)) := by
 rw [LibSignalReference.Proofs.AesLayout.bitslice_network]
 simp only [bind_tc_ok, actual_inverse_network]
end LibSignalReference.Candidate.AesInverseCircuit
