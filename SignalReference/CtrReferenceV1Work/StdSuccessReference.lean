import CtrReferenceV1Work.StateReference
import CtrReferenceV1Work.ConversionReference
namespace LibSignalReference.Candidate.CtrStdSuccess
open Aeneas Aeneas.Std
/-- These are typed external value models; no owned-Drop/Err behavior theorem. -/
theorem literal_same (s : String) (h : s.toByteArray.size ≤ U32.max) :
 _root_.CtrStateV1.toStr s h = Aeneas.Std.toStr s h := rfl

theorem result_ok_success (value : Usize) :
 _root_.CtrStateV1.core.result.specialized_Type_39cefb7ef8c35a912b46372529760af6dab6d475787219ce914c64da40f08098.ok.specialized_Fun_a5d5674905ed002026d02685176bd5313ee0fdbe48d12a6d7a8a9a2595c3e604 (_root_.CtrStateV1.core.result.Result.specialized_Type_39cefb7ef8c35a912b46372529760af6dab6d475787219ce914c64da40f08098.Ok value) = .ok (_root_.CtrStateV1.core.option.Option.specialized_Type_2455b8227f1e194b0fb8fba8e6015cc477b54ea44dfb19ba33823a6f9afbc8e4.Some value) := rfl

theorem expect_success (value : Array U8 (4#usize)) (message : Str) :
 _root_.CtrStateV1.core.result.specialized_Type_a7e80a29bad05fedc15b2d585d4897c71be4c4f509da8e7ad89a2001d247cdf1.expect.specialized_Fun_338edf893cdb37a850b70bb7354c6f524e262d4b8294a2e77f65ecf4505d1fcc (_root_.CtrStateV1.core.result.Result.specialized_Type_a7e80a29bad05fedc15b2d585d4897c71be4c4f509da8e7ad89a2001d247cdf1.Ok value) message = .ok value := rfl

theorem slice_copy_four (value : Array U8 (4#usize)) :
 _root_.CtrStateV1.SharedSliceU8.Insts.CoreConvertTryIntoArrayU84.try_into value.to_slice =
 .ok (_root_.CtrStateV1.core.result.Result.specialized_Type_a7e80a29bad05fedc15b2d585d4897c71be4c4f509da8e7ad89a2001d247cdf1.Ok value) := by
 simp [_root_.CtrStateV1.SharedSliceU8.Insts.CoreConvertTryIntoArrayU84.try_into,
   core.array.TryFromArrayCopySlice.try_from, Array.to_slice, Slice.len]

theorem actual_widen_success (value : U32) :
 _root_.CtrStateV1.U32.Insts.CoreConvertTryIntoUsize.try_into value =
 .ok (_root_.CtrStateV1.core.result.Result.specialized_Type_39cefb7ef8c35a912b46372529760af6dab6d475787219ce914c64da40f08098.Ok (UScalar.cast .Usize value)) := by
 simp [_root_.CtrStateV1.U32.Insts.CoreConvertTryIntoUsize.try_into,
   LibSignalReference.Candidate.CtrConversionV1.actual_widen_ok]
end LibSignalReference.Candidate.CtrStdSuccess
