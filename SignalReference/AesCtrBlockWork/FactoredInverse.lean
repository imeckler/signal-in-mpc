import AesCtrBlockWork.InverseWritebackLemmas
namespace LibSignalReference.Candidate.AesInverseComposition
open Aeneas Aeneas.Std
open LibSignalReference.Proofs.AesLayout
open TlsMpc.Signal.AesLayout
open LibSignalReference.Candidate.AesCtrInverse
open LibSignalReference.Candidate.AesInverseWriteback
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

def columnsResult (t0 t1 t2 t3 t4 t5 t6 t7 : U64) : Batch :=
 ⟨[blockArray t0.bv t4.bv,blockArray t1.bv t5.bv,blockArray t2.bv t6.bv,blockArray t3.bv t7.bv],by simp⟩
def writeAll (t0 t1 t2 t3 t4 t5 t6 t7 : U64) : Result Batch := do
 let output←RustCryptoAesCtrInverse.hybrid_array.Array.specialized_Type_466e03121b73c7d435361c7adc904649fbf81c760e593c61b65a8532a101fdf5.Insts.CoreDefaultDefault.default
 let output←putPair output (0#usize) t0 t4
 let output←putPair output (1#usize) t1 t5
 let output←putPair output (2#usize) t2 t6
 putPair output (3#usize) t3 t7

theorem writeAll_correct (t0 t1 t2 t3 t4 t5 t6 t7 : U64) :
 writeAll t0 t1 t2 t3 t4 t5 t6 t7 = .ok (columnsResult t0 t1 t2 t3 t4 t5 t6 t7) := by
 have hz : zeroBatch=batchInput (fun _=>inputBlock (fun _=>0#u8)) := by with_unfolding_all rfl
 simp only [writeAll,default_batch,hz,bind_tc_ok]
 rw [put_pair_0]
 simp only [bind_tc_ok]
 rw [put_pair_1]
 simp only [bind_tc_ok]
 rw [put_pair_2]
 simp only [bind_tc_ok]
 rw [put_pair_3]
 rfl

/-- Proof-only source factor. Every delta/assert/read is retained; the eight
actual nested writes are grouped by associativity into four proved pairs. -/
def factoredInverse (input : Slice U64) : Result Batch := do
  let left_val ←
    RustCryptoAesCtrInverse.core.slice.SliceU64.len.specialized_Fun_119f09e8f72b57b7623987b9b0f893bbea4ce9fea982447bc97cd7147a229fe0
      input
  massert (left_val = 8#usize)
  let t0 ← Slice.index_usize input 0#usize
  let t1 ← Slice.index_usize input 1#usize
  let t2 ← Slice.index_usize input 2#usize
  let t3 ← Slice.index_usize input 3#usize
  let t4 ← Slice.index_usize input 4#usize
  let t5 ← Slice.index_usize input 5#usize
  let t6 ← Slice.index_usize input 6#usize
  let t7 ← Slice.index_usize input 7#usize
  let (t11, t01) ←
    RustCryptoAesCtrInverse.soft.fixslice.delta_swap_2 t1 t0 1#u32 6148914691236517205#u64
  let (t31, t21) ←
    RustCryptoAesCtrInverse.soft.fixslice.delta_swap_2 t3 t2 1#u32 6148914691236517205#u64
  let (t51, t41) ←
    RustCryptoAesCtrInverse.soft.fixslice.delta_swap_2 t5 t4 1#u32 6148914691236517205#u64
  let (t71, t61) ←
    RustCryptoAesCtrInverse.soft.fixslice.delta_swap_2 t7 t6 1#u32 6148914691236517205#u64
  let (t22, t02) ←
    RustCryptoAesCtrInverse.soft.fixslice.delta_swap_2 t21 t01 2#u32 3689348814741910323#u64
  let (t32, t12) ←
    RustCryptoAesCtrInverse.soft.fixslice.delta_swap_2 t31 t11 2#u32 3689348814741910323#u64
  let (t62, t42) ←
    RustCryptoAesCtrInverse.soft.fixslice.delta_swap_2 t61 t41 2#u32 3689348814741910323#u64
  let (t72, t52) ←
    RustCryptoAesCtrInverse.soft.fixslice.delta_swap_2 t71 t51 2#u32 3689348814741910323#u64
  let (t43, t03) ←
    RustCryptoAesCtrInverse.soft.fixslice.delta_swap_2 t42 t02 4#u32 1085102592571150095#u64
  let (t53, t13) ←
    RustCryptoAesCtrInverse.soft.fixslice.delta_swap_2 t52 t12 4#u32 1085102592571150095#u64
  let (t63, t23) ←
    RustCryptoAesCtrInverse.soft.fixslice.delta_swap_2 t62 t22 4#u32 1085102592571150095#u64
  let (t73, t33) ←
    RustCryptoAesCtrInverse.soft.fixslice.delta_swap_2 t72 t32 4#u32 1085102592571150095#u64
  writeAll t03 t13 t23 t33 t43 t53 t63 t73

theorem factor_exact (input : Slice U64) :
 RustCryptoAesCtrInverse.soft.fixslice.inv_bitslice input = factoredInverse input := by
 with_unfolding_all simp only [RustCryptoAesCtrInverse.soft.fixslice.inv_bitslice,
   factoredInverse,writeAll,putPair,putRange,writeRange,bind_assoc_eq,uncurry,bind_tc_ok]
 with_unfolding_all simp only [uncurry_apply_pair, bind_eq_iff, Prod.forall, bind_assoc_eq, bind_tc_ok]

 repeat' (first | (intro) | dsimp (config := {zeta := true, iota := true, beta := true}) only [] | simp only [uncurry_apply_pair, bind_eq_iff, Prod.forall, bind_assoc_eq, bind_tc_ok])

theorem actual_inverse (words : Words (BitVec 64)) :
 RustCryptoAesCtrInverse.soft.fixslice.inv_bitslice (wordSlice words) = .ok (inverseResult words) := by
 rw [factor_exact]
 have hlen (hx : 8 < 2 ^ UScalarTy.Usize.numBits) : Usize.ofNatCore 8 hx = 8#usize := by scalar_tac
 simp [factoredInverse,
   RustCryptoAesCtrInverse.core.slice.SliceU64.len.specialized_Fun_119f09e8f72b57b7623987b9b0f893bbea4ce9fea982447bc97cd7147a229fe0,
   wordSlice, Words.list, Slice.len, Slice.index_usize, hlen, massert, LibSignalReference.Candidate.AesCtrInverse.delta_refines, writeAll_correct,
   inverseResult, columnsResult, transpose]
end LibSignalReference.Candidate.AesInverseComposition
