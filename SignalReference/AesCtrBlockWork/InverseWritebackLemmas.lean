import AesCtrBlockWork.InverseReference
namespace LibSignalReference.Candidate.AesInverseWriteback
open Aeneas Aeneas.Std
open LibSignalReference.Proofs.AesLayout
open LibSignalReference.Proofs.AesInverseWrite
open LibSignalReference.Candidate.AesCtrInverse
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

def inputBlock (initial : Nat→U8) : Array U8 (16#usize) :=
 ⟨[initial 0,initial 1,initial 2,initial 3,initial 4,initial 5,initial 6,initial 7,
   initial 8,initial 9,initial 10,initial 11,initial 12,initial 13,initial 14,initial 15],by simp⟩

def writeRange (block : Array U8 (16#usize)) (start stop : Usize) (column : U64) :
 Result (Array U8 (16#usize)) := do
 let (slice,back)←RustCryptoAesCtrInverse.hybrid_array.Array.specialized_Type_f6d0079c9d47818b2c760c13dc530abd0fcf2330bbf625eeaa753c4e448e7d5f.Insts.CoreOpsIndexIndexMutspecialized_Type_a6d41e09652f1286a20c9e5d6cdaa143f56a848c0ded3779accf5fbb4661efb9.index_mut block {start:=start,«end»:=stop}
 let changed←RustCryptoAesCtrInverse.soft.fixslice.inv_bitslice.write_reordered column slice
 .ok (back changed)

def afterFirst (initial : Nat→U8) (column : U64) : Array U8 (16#usize) :=
 ⟨(TlsMpc.Signal.AesInverseWrite.value column.bv (fun i=>(initial i).bv)).map (fun byte=>(⟨byte⟩ : U8)) ++
   [initial 12,initial 13,initial 14,initial 15],by simp [TlsMpc.Signal.AesInverseWrite.value]⟩

theorem first_write (initial : Nat→U8) (column : U64) :
 writeRange (inputBlock initial) (0#usize) (12#usize) column = .ok (afterFirst initial column) := by
 simp [writeRange,
  RustCryptoAesCtrInverse.hybrid_array.Array.specialized_Type_f6d0079c9d47818b2c760c13dc530abd0fcf2330bbf625eeaa753c4e448e7d5f.Insts.CoreOpsIndexIndexMutspecialized_Type_a6d41e09652f1286a20c9e5d6cdaa143f56a848c0ded3779accf5fbb4661efb9.index_mut,
  RustCryptoAesCtrInverse.hybrid_array.specialized_Type_f6d0079c9d47818b2c760c13dc530abd0fcf2330bbf625eeaa753c4e448e7d5f.as_mut_slice.specialized_Fun_fa49050490a6794932845a12ade3002a418c61a22f1911911b223e0c1dbb9454,
  RustCryptoAesCtrInverse.SliceU8.Insts.CoreOpsIndexIndexMutspecialized_Type_a6d41e09652f1286a20c9e5d6cdaa143f56a848c0ded3779accf5fbb4661efb9.index_mut,
  Array.to_slice_mut,core.slice.index.SliceIndexRangeUsizeSlice.index_mut,inputBlock]
 with_unfolding_all erw [LibSignalReference.Candidate.AesCtrInverse.write_refines column initial]
 simp [afterFirst,resultSlice,TlsMpc.Signal.AesInverseWrite.value,Array.from_slice,List.setSlice!,lift]
def secondInitial (initial : Nat→U8) (column : U64) : Nat→U8
 | 4 => ⟨column.bv.extractLsb' 8 8⟩
 | 5 => ⟨column.bv.extractLsb' 24 8⟩
 | 6 => ⟨column.bv.extractLsb' 40 8⟩
 | 7 => ⟨column.bv.extractLsb' 56 8⟩
 | i => initial (i+4)

theorem second_write (initial : Nat→U8) (lo hi : U64) :
 writeRange (afterFirst initial lo) (4#usize) (16#usize) hi = .ok (blockArray lo.bv hi.bv) := by
 simp [writeRange,
  RustCryptoAesCtrInverse.hybrid_array.Array.specialized_Type_f6d0079c9d47818b2c760c13dc530abd0fcf2330bbf625eeaa753c4e448e7d5f.Insts.CoreOpsIndexIndexMutspecialized_Type_a6d41e09652f1286a20c9e5d6cdaa143f56a848c0ded3779accf5fbb4661efb9.index_mut,
  RustCryptoAesCtrInverse.hybrid_array.specialized_Type_f6d0079c9d47818b2c760c13dc530abd0fcf2330bbf625eeaa753c4e448e7d5f.as_mut_slice.specialized_Fun_fa49050490a6794932845a12ade3002a418c61a22f1911911b223e0c1dbb9454,
  RustCryptoAesCtrInverse.SliceU8.Insts.CoreOpsIndexIndexMutspecialized_Type_a6d41e09652f1286a20c9e5d6cdaa143f56a848c0ded3779accf5fbb4661efb9.index_mut,
  Array.to_slice_mut,core.slice.index.SliceIndexRangeUsizeSlice.index_mut,afterFirst,TlsMpc.Signal.AesInverseWrite.value]

 with_unfolding_all erw [LibSignalReference.Candidate.AesCtrInverse.write_refines hi (secondInitial initial lo)]
 with_unfolding_all rfl

def writePair (block : Array U8 (16#usize)) (lo hi : U64) : Result (Array U8 (16#usize)) := do
 let first←writeRange block (0#usize) (12#usize) lo
 writeRange first (4#usize) (16#usize) hi

theorem pair_write_input (initial : Nat→U8) (lo hi : U64) :
 writePair (inputBlock initial) lo hi = .ok (blockArray lo.bv hi.bv) := by
 simp only [writePair,first_write,bind_tc_ok,second_write]
theorem input_range (initial : Nat→U8) :
 (inputBlock initial).val = (List.range 16).map initial := by
 simp [inputBlock,List.range_succ]

theorem input_all (block : Array U8 (16#usize)) :
 inputBlock (fun i=>block.val[i]?.getD (0#u8)) = block := by
 apply Subtype.ext
 rw [input_range]
 have hlen : block.val.length=16 := by simpa using block.property
 apply List.ext_getElem
 · simp [hlen]
 · intro index hleft hright
   simp only [List.getElem_map,List.getElem_range,List.getElem?_eq_getElem hright,Option.getD_some]

theorem pair_write_all (block : Array U8 (16#usize)) (lo hi : U64) :
 writePair block lo hi = .ok (blockArray lo.bv hi.bv) := by
 simpa only [input_all] using pair_write_input (fun i=>block.val[i]?.getD (0#u8)) lo hi
abbrev Block16 := Array U8 (16#usize)
abbrev Batch := RustCryptoAesCtrInverse.hybrid_array.Array.specialized_Type_466e03121b73c7d435361c7adc904649fbf81c760e593c61b65a8532a101fdf5
def batchInput (blocks : Nat→Block16) : Batch :=
 ⟨[blocks 0,blocks 1,blocks 2,blocks 3],by simp⟩
def putRange (batch : Batch) (index start stop : Usize) (column : U64) : Result Batch := do
 let (block,back)←RustCryptoAesCtrInverse.hybrid_array.Array.specialized_Type_466e03121b73c7d435361c7adc904649fbf81c760e593c61b65a8532a101fdf5.Insts.CoreOpsIndexIndexMutUsize.index_mut batch index
 let changed←writeRange block start stop column
 .ok (back changed)
def putPair (batch : Batch) (index : Usize) (lo hi : U64) : Result Batch := do
 let first←putRange batch index (0#usize) (12#usize) lo
 putRange first index (4#usize) (16#usize) hi

theorem put_pair_0 (blocks : Nat→Block16) (lo hi : U64) :
 putPair (batchInput blocks) (0#usize) lo hi =
 .ok (batchInput (fun i=>if i=0 then blockArray lo.bv hi.bv else blocks i)) := by
 have context := congrArg (fun result : Result Block16 => do
   let output←result
   .ok (batchInput (fun i=>if i=0 then output else blocks i))) (pair_write_all (blocks 0) lo hi)
 with_unfolding_all simpa [putPair,putRange,writePair,batchInput,
  RustCryptoAesCtrInverse.hybrid_array.Array.specialized_Type_466e03121b73c7d435361c7adc904649fbf81c760e593c61b65a8532a101fdf5.Insts.CoreOpsIndexIndexMutUsize.index_mut,RustCryptoAesCtrInverse.hybrid_array.specialized_Type_466e03121b73c7d435361c7adc904649fbf81c760e593c61b65a8532a101fdf5.as_mut_slice.specialized_Fun_a6180b7c4a0a7b5b08e019a3fd707d007e0f22c30533e51bacf90c12e87aff48,RustCryptoAesCtrInverse.Slicespecialized_Type_f6d0079c9d47818b2c760c13dc530abd0fcf2330bbf625eeaa753c4e448e7d5f.Insts.CoreOpsIndexIndexMutUsize.index_mut,
  Array.to_slice_mut,Array.from_slice,Slice.index_mut_usize,Slice.index_usize,Slice.set,Slice.setAtNat]
  using context
theorem put_pair_1 (blocks : Nat→Block16) (lo hi : U64) :
 putPair (batchInput blocks) (1#usize) lo hi =
 .ok (batchInput (fun i=>if i=1 then blockArray lo.bv hi.bv else blocks i)) := by
 have context := congrArg (fun result : Result Block16 => do
   let output←result
   .ok (batchInput (fun i=>if i=1 then output else blocks i))) (pair_write_all (blocks 1) lo hi)
 with_unfolding_all simpa [putPair,putRange,writePair,batchInput,
  RustCryptoAesCtrInverse.hybrid_array.Array.specialized_Type_466e03121b73c7d435361c7adc904649fbf81c760e593c61b65a8532a101fdf5.Insts.CoreOpsIndexIndexMutUsize.index_mut,RustCryptoAesCtrInverse.hybrid_array.specialized_Type_466e03121b73c7d435361c7adc904649fbf81c760e593c61b65a8532a101fdf5.as_mut_slice.specialized_Fun_a6180b7c4a0a7b5b08e019a3fd707d007e0f22c30533e51bacf90c12e87aff48,RustCryptoAesCtrInverse.Slicespecialized_Type_f6d0079c9d47818b2c760c13dc530abd0fcf2330bbf625eeaa753c4e448e7d5f.Insts.CoreOpsIndexIndexMutUsize.index_mut,
  Array.to_slice_mut,Array.from_slice,Slice.index_mut_usize,Slice.index_usize,Slice.set,Slice.setAtNat]
  using context
theorem put_pair_2 (blocks : Nat→Block16) (lo hi : U64) :
 putPair (batchInput blocks) (2#usize) lo hi =
 .ok (batchInput (fun i=>if i=2 then blockArray lo.bv hi.bv else blocks i)) := by
 have context := congrArg (fun result : Result Block16 => do
   let output←result
   .ok (batchInput (fun i=>if i=2 then output else blocks i))) (pair_write_all (blocks 2) lo hi)
 with_unfolding_all simpa [putPair,putRange,writePair,batchInput,
  RustCryptoAesCtrInverse.hybrid_array.Array.specialized_Type_466e03121b73c7d435361c7adc904649fbf81c760e593c61b65a8532a101fdf5.Insts.CoreOpsIndexIndexMutUsize.index_mut,RustCryptoAesCtrInverse.hybrid_array.specialized_Type_466e03121b73c7d435361c7adc904649fbf81c760e593c61b65a8532a101fdf5.as_mut_slice.specialized_Fun_a6180b7c4a0a7b5b08e019a3fd707d007e0f22c30533e51bacf90c12e87aff48,RustCryptoAesCtrInverse.Slicespecialized_Type_f6d0079c9d47818b2c760c13dc530abd0fcf2330bbf625eeaa753c4e448e7d5f.Insts.CoreOpsIndexIndexMutUsize.index_mut,
  Array.to_slice_mut,Array.from_slice,Slice.index_mut_usize,Slice.index_usize,Slice.set,Slice.setAtNat]
  using context
theorem put_pair_3 (blocks : Nat→Block16) (lo hi : U64) :
 putPair (batchInput blocks) (3#usize) lo hi =
 .ok (batchInput (fun i=>if i=3 then blockArray lo.bv hi.bv else blocks i)) := by
 have context := congrArg (fun result : Result Block16 => do
   let output←result
   .ok (batchInput (fun i=>if i=3 then output else blocks i))) (pair_write_all (blocks 3) lo hi)
 with_unfolding_all simpa [putPair,putRange,writePair,batchInput,
  RustCryptoAesCtrInverse.hybrid_array.Array.specialized_Type_466e03121b73c7d435361c7adc904649fbf81c760e593c61b65a8532a101fdf5.Insts.CoreOpsIndexIndexMutUsize.index_mut,RustCryptoAesCtrInverse.hybrid_array.specialized_Type_466e03121b73c7d435361c7adc904649fbf81c760e593c61b65a8532a101fdf5.as_mut_slice.specialized_Fun_a6180b7c4a0a7b5b08e019a3fd707d007e0f22c30533e51bacf90c12e87aff48,RustCryptoAesCtrInverse.Slicespecialized_Type_f6d0079c9d47818b2c760c13dc530abd0fcf2330bbf625eeaa753c4e448e7d5f.Insts.CoreOpsIndexIndexMutUsize.index_mut,
  Array.to_slice_mut,Array.from_slice,Slice.index_mut_usize,Slice.index_usize,Slice.set,Slice.setAtNat]
  using context
end LibSignalReference.Candidate.AesInverseWriteback
