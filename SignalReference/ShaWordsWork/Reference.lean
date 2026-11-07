import ShaWordsWork.Generated.Funs
import TlsMpc.ByteCircuit

namespace LibSignalReference.Candidate.ShaWords

open Aeneas Aeneas.Std TlsMpc TlsMpc.Sha256
open RustCryptoSha256ToWords

def chunk (block : Array U8 64#usize) (index : Fin 16) : Array U8 4#usize :=
  ⟨(block.val.drop (4 * index.val)).take 4, by simp; omega⟩

theorem closure_result (block : Array U8 64#usize) (index : Usize) (hi : index.val < 16) :
    sha256.soft.to_u32s.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut block index =
      .ok (core.num.U32.from_be_bytes (chunk block ⟨index.val, hi⟩), block) := by
  have hmax : (4#usize).val * index.val ≤ Usize.max := by scalar_tac
  obtain ⟨offset, hoff, hval⟩ := WP.spec_imp_exists (Usize.mul_spec (x := 4#usize) (y := index) hmax)
  have hval' : offset.val = 4 * index.val := by simpa using hval
  have hlo : offset.val ≤ block.val.length := by simp; omega
  have hhi : 4 ≤ (block.val.drop offset.val).length := by simp; omega
  have hlo' : 4 * index.val ≤ 64 := by omega
  have hhi' : 4 ≤ 64 - 4 * index.val := by omega
  simp only [sha256.soft.to_u32s.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut,
    hoff, bind_tc_ok]
  simp [core.array.Array.index, core.ops.index.IndexSlice, core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeFromUsizeSlice, core.slice.index.SliceIndexRangeFromUsizeSlice.index,
    core.slice.index.SliceIndexRangeToUsizeSlice, core.slice.index.SliceIndexRangeToUsizeSlice.index,
    Array.to_slice, Slice.drop, hlo, hhi, core.array.TryFromArrayCopySlice.try_from,
    core.result.Result.unwrap, Slice.length, List.slice, chunk, hval', lift, hlo', hhi']

end LibSignalReference.Candidate.ShaWords

#print axioms LibSignalReference.Candidate.ShaWords.closure_result
