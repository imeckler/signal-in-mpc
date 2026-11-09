-- AUTHORED external fixed-content bindings (not generated source computations).
-- [signal_ctr_reference]: external functions.
-- Std content models, not allocator/Drop/erasure. Native endian: pinned little-endian.
-- Typed expect Err model records panic only; proof supports Ok paths exclusively.
-- No generic owned-Drop or panic-formatting equivalence is claimed.
import Aeneas
import CtrReferenceV1Work.Generated.ConversionFinal.Funs
import CtrReferenceV1Work.Generated.StateUnifiedV1.Types
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048
namespace CtrStateV1
-- Same Std toStr value, with a kernel-computed default bound proof.
def toStr (s : String) (h : s.toByteArray.size ≤ U32.max := by simp only [U32.max, U32.numBits]; decide) : Str := Aeneas.Std.toStr s h
theorem toStr_value (s : String) (h : s.toByteArray.size ≤ U32.max) : toStr s h = Aeneas.Std.toStr s h := rfl


/-- [core::convert::{impl core::convert::TryInto<usize> for u32}::try_into::specialized_Fun_c5120b84e151282462524ed73a6208de4eaa6bd159ac3403ae535cedfd532c01]:
    Source: '/rustc/library/core/src/convert/mod.rs', lines 821:4-821:44
    Name pattern: [core::convert::{core::convert::TryInto<u32, usize>}::try_into::specialized_Fun_c5120b84e151282462524ed73a6208de4eaa6bd159ac3403ae535cedfd532c01]
    Visibility: public -/
@[rust_fun
  "core::convert::{core::convert::TryInto<u32, usize>}::try_into::specialized_Fun_c5120b84e151282462524ed73a6208de4eaa6bd159ac3403ae535cedfd532c01"]
def U32.Insts.CoreConvertTryIntoUsize.try_into : Std.U32 → Result
    core.result.Result.specialized_Type_39cefb7ef8c35a912b46372529760af6dab6d475787219ce914c64da40f08098 :=
  fun value => do
    let result ← CtrConversionV1.Usize.Insts.CoreConvertTryFromU32TryFromIntError.try_from value
    .ok (match result with | .Ok a => core.result.Result.specialized_Type_39cefb7ef8c35a912b46372529760af6dab6d475787219ce914c64da40f08098.Ok a | .Err e => core.result.Result.specialized_Type_39cefb7ef8c35a912b46372529760af6dab6d475787219ce914c64da40f08098.Err e)

/-- [core::convert::{impl core::convert::TryInto<[u8; 4usize]> for &'_ [u8]}::try_into::specialized_Fun_87fbdcb6610118279402ad683b25d2e7f7c5c1d7f8731cdb1657da0550035a43]:
    Source: '/rustc/library/core/src/convert/mod.rs', lines 821:4-821:44
    Name pattern: [core::convert::{core::convert::TryInto<&'_ [u8], [u8; 4]>}::try_into::specialized_Fun_87fbdcb6610118279402ad683b25d2e7f7c5c1d7f8731cdb1657da0550035a43]
    Visibility: public -/
@[rust_fun
  "core::convert::{core::convert::TryInto<&'_ [u8], [u8; 4]>}::try_into::specialized_Fun_87fbdcb6610118279402ad683b25d2e7f7c5c1d7f8731cdb1657da0550035a43"]
def SharedSliceU8.Insts.CoreConvertTryIntoArrayU84.try_into : Slice Std.U8 → Result
    core.result.Result.specialized_Type_a7e80a29bad05fedc15b2d585d4897c71be4c4f509da8e7ad89a2001d247cdf1 :=
  fun value => do
    let result ← Aeneas.Std.core.array.TryFromArrayCopySlice.try_from (4#usize) Aeneas.Std.core.marker.CopyU8 value
    .ok (match result with | .Ok a => core.result.Result.specialized_Type_a7e80a29bad05fedc15b2d585d4897c71be4c4f509da8e7ad89a2001d247cdf1.Ok a | .Err e => core.result.Result.specialized_Type_a7e80a29bad05fedc15b2d585d4897c71be4c4f509da8e7ad89a2001d247cdf1.Err e)

/-- [core::iter::range::{impl core::iter::traits::iterator::Iterator for core::ops::range::Range::specialized_Type_a6d41e09652f1286a20c9e5d6cdaa143f56a848c0ded3779accf5fbb4661efb9}::next::specialized_Fun_f3a5d9a3d455fdb9f1e98e5aa6ba30afdf59ca57118117fad7b30f667dbb6e49]:
    Source: '/rustc/library/core/src/iter/range.rs', lines 1184:4-1184:35
    Name pattern: [core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::Range::specialized_Type_a6d41e09652f1286a20c9e5d6cdaa143f56a848c0ded3779accf5fbb4661efb9>}::next::specialized_Fun_f3a5d9a3d455fdb9f1e98e5aa6ba30afdf59ca57118117fad7b30f667dbb6e49]
    Visibility: public -/
@[rust_fun
  "core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::Range::specialized_Type_a6d41e09652f1286a20c9e5d6cdaa143f56a848c0ded3779accf5fbb4661efb9>}::next::specialized_Fun_f3a5d9a3d455fdb9f1e98e5aa6ba30afdf59ca57118117fad7b30f667dbb6e49"]
def core.ops.range.Range.specialized_Type_a6d41e09652f1286a20c9e5d6cdaa143f56a848c0ded3779accf5fbb4661efb9.Insts.CoreIterTraitsIteratorIterator.next : core.ops.range.Range.specialized_Type_a6d41e09652f1286a20c9e5d6cdaa143f56a848c0ded3779accf5fbb4661efb9
    → Result
    (core.option.Option.specialized_Type_2455b8227f1e194b0fb8fba8e6015cc477b54ea44dfb19ba33823a6f9afbc8e4
    ×
    core.ops.range.Range.specialized_Type_a6d41e09652f1286a20c9e5d6cdaa143f56a848c0ded3779accf5fbb4661efb9) :=
  fun range => do
    let (choice,next) ← Aeneas.Std.core.iter.range.IteratorRange.next
      (Aeneas.Std.core.iter.range.UScalarStep .Usize Aeneas.Std.core.clone.CloneUsize Aeneas.Std.core.cmp.PartialOrdUsize)
      {start:=range.start, «end»:=range.end}
    pure ((match choice with | none => core.option.Option.specialized_Type_2455b8227f1e194b0fb8fba8e6015cc477b54ea44dfb19ba33823a6f9afbc8e4.None | some value => core.option.Option.specialized_Type_2455b8227f1e194b0fb8fba8e6015cc477b54ea44dfb19ba33823a6f9afbc8e4.Some value),
      {start:=next.start, «end»:=next.end})

/-- [core::iter::traits::collect::{impl core::iter::traits::collect::IntoIterator for core::ops::range::Range::specialized_Type_a6d41e09652f1286a20c9e5d6cdaa143f56a848c0ded3779accf5fbb4661efb9}::into_iter::specialized_Fun_b63c6015497457cf43133a5f8e0ec41bc4205170d205521ebf560cd0c4f2f0d8]:
    Source: '/rustc/library/core/src/iter/traits/collect.rs', lines 322:4-322:27
    Name pattern: [core::iter::traits::collect::{core::iter::traits::collect::IntoIterator<core::ops::range::Range::specialized_Type_a6d41e09652f1286a20c9e5d6cdaa143f56a848c0ded3779accf5fbb4661efb9>}::into_iter::specialized_Fun_b63c6015497457cf43133a5f8e0ec41bc4205170d205521ebf560cd0c4f2f0d8]
    Visibility: public -/
@[rust_fun
  "core::iter::traits::collect::{core::iter::traits::collect::IntoIterator<core::ops::range::Range::specialized_Type_a6d41e09652f1286a20c9e5d6cdaa143f56a848c0ded3779accf5fbb4661efb9>}::into_iter::specialized_Fun_b63c6015497457cf43133a5f8e0ec41bc4205170d205521ebf560cd0c4f2f0d8"]
def core.ops.range.Range.specialized_Type_a6d41e09652f1286a20c9e5d6cdaa143f56a848c0ded3779accf5fbb4661efb9.Insts.CoreIterTraitsCollectIntoIterator.into_iter : core.ops.range.Range.specialized_Type_a6d41e09652f1286a20c9e5d6cdaa143f56a848c0ded3779accf5fbb4661efb9
    → Result
    core.ops.range.Range.specialized_Type_a6d41e09652f1286a20c9e5d6cdaa143f56a848c0ded3779accf5fbb4661efb9 :=
  fun range => .ok range

/-- [core::num::{u32}::to_ne_bytes]:
    Source: '/rustc/library/core/src/num/uint_macros.rs', lines 4055:8-4055:65
    Name pattern: [core::num::{u32}::to_ne_bytes]
    Visibility: public -/
@[rust_fun "core::num::{u32}::to_ne_bytes"]
def core.num.U32.to_ne_bytes : Std.U32 → Result (Array Std.U8 4#usize) :=
  fun value => .ok (Aeneas.Std.core.num.U32.to_le_bytes value)

/-- [core::num::{u32}::from_ne_bytes]:
    Source: '/rustc/library/core/src/num/uint_macros.rs', lines 4158:8-4158:74
    Name pattern: [core::num::{u32}::from_ne_bytes]
    Visibility: public -/
@[rust_fun "core::num::{u32}::from_ne_bytes"]
def core.num.U32.from_ne_bytes : Array Std.U8 4#usize → Result Std.U32 :=
  fun value => .ok (Aeneas.Std.core.num.U32.from_le_bytes value)

/-- [core::result::{core::result::Result::specialized_Type_39cefb7ef8c35a912b46372529760af6dab6d475787219ce914c64da40f08098}::ok::specialized_Fun_a5d5674905ed002026d02685176bd5313ee0fdbe48d12a6d7a8a9a2595c3e604]:
    Source: '/rustc/library/core/src/result.rs', lines 709:4-712:28
    Name pattern: [core::result::{core::result::Result::specialized_Type_39cefb7ef8c35a912b46372529760af6dab6d475787219ce914c64da40f08098}::ok::specialized_Fun_a5d5674905ed002026d02685176bd5313ee0fdbe48d12a6d7a8a9a2595c3e604]
    Visibility: public -/
@[rust_fun
  "core::result::{core::result::Result::specialized_Type_39cefb7ef8c35a912b46372529760af6dab6d475787219ce914c64da40f08098}::ok::specialized_Fun_a5d5674905ed002026d02685176bd5313ee0fdbe48d12a6d7a8a9a2595c3e604"]
def core.result.specialized_Type_39cefb7ef8c35a912b46372529760af6dab6d475787219ce914c64da40f08098.ok.specialized_Fun_a5d5674905ed002026d02685176bd5313ee0fdbe48d12a6d7a8a9a2595c3e604 : core.result.Result.specialized_Type_39cefb7ef8c35a912b46372529760af6dab6d475787219ce914c64da40f08098
    → Result
    core.option.Option.specialized_Type_2455b8227f1e194b0fb8fba8e6015cc477b54ea44dfb19ba33823a6f9afbc8e4 :=
  fun value => .ok (match value with | core.result.Result.specialized_Type_39cefb7ef8c35a912b46372529760af6dab6d475787219ce914c64da40f08098.Ok a => core.option.Option.specialized_Type_2455b8227f1e194b0fb8fba8e6015cc477b54ea44dfb19ba33823a6f9afbc8e4.Some a | core.result.Result.specialized_Type_39cefb7ef8c35a912b46372529760af6dab6d475787219ce914c64da40f08098.Err _ => core.option.Option.specialized_Type_2455b8227f1e194b0fb8fba8e6015cc477b54ea44dfb19ba33823a6f9afbc8e4.None)

/-- [core::result::{core::result::Result::specialized_Type_a7e80a29bad05fedc15b2d585d4897c71be4c4f509da8e7ad89a2001d247cdf1}::expect::specialized_Fun_338edf893cdb37a850b70bb7354c6f524e262d4b8294a2e77f65ecf4505d1fcc]:
    Source: '/rustc/library/core/src/result.rs', lines 1178:4-1180:22
    Name pattern: [core::result::{core::result::Result::specialized_Type_a7e80a29bad05fedc15b2d585d4897c71be4c4f509da8e7ad89a2001d247cdf1}::expect::specialized_Fun_338edf893cdb37a850b70bb7354c6f524e262d4b8294a2e77f65ecf4505d1fcc]
    Visibility: public -/
@[rust_fun
  "core::result::{core::result::Result::specialized_Type_a7e80a29bad05fedc15b2d585d4897c71be4c4f509da8e7ad89a2001d247cdf1}::expect::specialized_Fun_338edf893cdb37a850b70bb7354c6f524e262d4b8294a2e77f65ecf4505d1fcc"]
def core.result.specialized_Type_a7e80a29bad05fedc15b2d585d4897c71be4c4f509da8e7ad89a2001d247cdf1.expect.specialized_Fun_338edf893cdb37a850b70bb7354c6f524e262d4b8294a2e77f65ecf4505d1fcc : core.result.Result.specialized_Type_a7e80a29bad05fedc15b2d585d4897c71be4c4f509da8e7ad89a2001d247cdf1
    → Str → Result (Array Std.U8 4#usize) :=
  fun value _ => match value with | core.result.Result.specialized_Type_a7e80a29bad05fedc15b2d585d4897c71be4c4f509da8e7ad89a2001d247cdf1.Ok a => .ok a | core.result.Result.specialized_Type_a7e80a29bad05fedc15b2d585d4897c71be4c4f509da8e7ad89a2001d247cdf1.Err _ => .fail .panic

/-- [core::slice::index::{impl core::ops::index::Index<core::ops::range::RangeFrom::specialized_Type_d1f2f41ce9b6a4bab41ab00dc2d7f45668cf5cd166e8302372ae9482af4f16f6> for [u8]}::index::specialized_Fun_f53a855b4fdaa436beda65996ad2d43bf3bf481a3897e3bd2e143b91c409f59b]:
    Source: '/rustc/library/core/src/slice/index.rs', lines 18:4-18:43
    Name pattern: [core::slice::index::{core::ops::index::Index<[u8], core::ops::range::RangeFrom::specialized_Type_d1f2f41ce9b6a4bab41ab00dc2d7f45668cf5cd166e8302372ae9482af4f16f6>}::index::specialized_Fun_f53a855b4fdaa436beda65996ad2d43bf3bf481a3897e3bd2e143b91c409f59b]
    Visibility: public -/
@[rust_fun
  "core::slice::index::{core::ops::index::Index<[u8], core::ops::range::RangeFrom::specialized_Type_d1f2f41ce9b6a4bab41ab00dc2d7f45668cf5cd166e8302372ae9482af4f16f6>}::index::specialized_Fun_f53a855b4fdaa436beda65996ad2d43bf3bf481a3897e3bd2e143b91c409f59b"]
def SliceU8.Insts.CoreOpsIndexIndexspecialized_Type_d1f2f41ce9b6a4bab41ab00dc2d7f45668cf5cd166e8302372ae9482af4f16f6.index : Slice Std.U8 →
    core.ops.range.RangeFrom.specialized_Type_d1f2f41ce9b6a4bab41ab00dc2d7f45668cf5cd166e8302372ae9482af4f16f6
    → Result (Slice Std.U8) :=
  fun value range => Aeneas.Std.core.slice.index.SliceIndexRangeFromUsizeSlice.index {start:=range.start} value

/-- [core::slice::index::{impl core::ops::index::Index<core::ops::range::RangeTo::specialized_Type_57510f1564d005eda0c45028821c0f658cf9a616f9dbf382cc9e92345d79bf26> for [u8]}::index::specialized_Fun_4ef7ea8f599750dff9e75d29081b15cf3bb8f3aa681043819b4c7de16767dbb3]:
    Source: '/rustc/library/core/src/slice/index.rs', lines 18:4-18:43
    Name pattern: [core::slice::index::{core::ops::index::Index<[u8], core::ops::range::RangeTo::specialized_Type_57510f1564d005eda0c45028821c0f658cf9a616f9dbf382cc9e92345d79bf26>}::index::specialized_Fun_4ef7ea8f599750dff9e75d29081b15cf3bb8f3aa681043819b4c7de16767dbb3]
    Visibility: public -/
@[rust_fun
  "core::slice::index::{core::ops::index::Index<[u8], core::ops::range::RangeTo::specialized_Type_57510f1564d005eda0c45028821c0f658cf9a616f9dbf382cc9e92345d79bf26>}::index::specialized_Fun_4ef7ea8f599750dff9e75d29081b15cf3bb8f3aa681043819b4c7de16767dbb3"]
def SliceU8.Insts.CoreOpsIndexIndexspecialized_Type_57510f1564d005eda0c45028821c0f658cf9a616f9dbf382cc9e92345d79bf26.index : Slice Std.U8 →
    core.ops.range.RangeTo.specialized_Type_57510f1564d005eda0c45028821c0f658cf9a616f9dbf382cc9e92345d79bf26
    → Result (Slice Std.U8) :=
  fun value range => Aeneas.Std.core.slice.index.SliceIndexRangeToUsizeSlice.index {«end»:=range.«end»} value

/-- [core::slice::index::{impl core::ops::index::Index<usize> for [u32]}::index::specialized_Fun_e4fa4824ca08485dd6a19a075bbea2ad81fe2441269e2264c435ffaad884dce1]:
    Source: '/rustc/library/core/src/slice/index.rs', lines 18:4-18:43
    Name pattern: [core::slice::index::{core::ops::index::Index<[u32], usize>}::index::specialized_Fun_e4fa4824ca08485dd6a19a075bbea2ad81fe2441269e2264c435ffaad884dce1]
    Visibility: public -/
@[rust_fun
  "core::slice::index::{core::ops::index::Index<[u32], usize>}::index::specialized_Fun_e4fa4824ca08485dd6a19a075bbea2ad81fe2441269e2264c435ffaad884dce1"]
def SliceU32.Insts.CoreOpsIndexIndexUsize.index : Slice Std.U32 → Std.Usize → Result Std.U32 :=
  fun value index => Aeneas.Std.Slice.index_usize value index

/-- [core::slice::index::{impl core::ops::index::IndexMut<core::ops::range::RangeFrom::specialized_Type_d1f2f41ce9b6a4bab41ab00dc2d7f45668cf5cd166e8302372ae9482af4f16f6> for [u8]}::index_mut::specialized_Fun_c258c8480741a7c354ea4b7d3df96e3d362ba9c7c708fc9e12729dd963581fd0]:
    Source: '/rustc/library/core/src/slice/index.rs', lines 31:4-31:55
    Name pattern: [core::slice::index::{core::ops::index::IndexMut<[u8], core::ops::range::RangeFrom::specialized_Type_d1f2f41ce9b6a4bab41ab00dc2d7f45668cf5cd166e8302372ae9482af4f16f6>}::index_mut::specialized_Fun_c258c8480741a7c354ea4b7d3df96e3d362ba9c7c708fc9e12729dd963581fd0]
    Visibility: public -/
@[rust_fun
  "core::slice::index::{core::ops::index::IndexMut<[u8], core::ops::range::RangeFrom::specialized_Type_d1f2f41ce9b6a4bab41ab00dc2d7f45668cf5cd166e8302372ae9482af4f16f6>}::index_mut::specialized_Fun_c258c8480741a7c354ea4b7d3df96e3d362ba9c7c708fc9e12729dd963581fd0"]
def SliceU8.Insts.CoreOpsIndexIndexMutspecialized_Type_d1f2f41ce9b6a4bab41ab00dc2d7f45668cf5cd166e8302372ae9482af4f16f6.index_mut : Slice Std.U8 →
    core.ops.range.RangeFrom.specialized_Type_d1f2f41ce9b6a4bab41ab00dc2d7f45668cf5cd166e8302372ae9482af4f16f6
    → Result ((Slice Std.U8) × (Slice Std.U8 → Slice Std.U8)) :=
  fun value range => Aeneas.Std.core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut {start:=range.start} value

/-- [core::slice::index::{impl core::ops::index::IndexMut<core::ops::range::RangeTo::specialized_Type_57510f1564d005eda0c45028821c0f658cf9a616f9dbf382cc9e92345d79bf26> for [u8]}::index_mut::specialized_Fun_6ccf858d2abc34cbf63867468726e02c008d2047a5652c9f9732359ee7248b29]:
    Source: '/rustc/library/core/src/slice/index.rs', lines 31:4-31:55
    Name pattern: [core::slice::index::{core::ops::index::IndexMut<[u8], core::ops::range::RangeTo::specialized_Type_57510f1564d005eda0c45028821c0f658cf9a616f9dbf382cc9e92345d79bf26>}::index_mut::specialized_Fun_6ccf858d2abc34cbf63867468726e02c008d2047a5652c9f9732359ee7248b29]
    Visibility: public -/
@[rust_fun
  "core::slice::index::{core::ops::index::IndexMut<[u8], core::ops::range::RangeTo::specialized_Type_57510f1564d005eda0c45028821c0f658cf9a616f9dbf382cc9e92345d79bf26>}::index_mut::specialized_Fun_6ccf858d2abc34cbf63867468726e02c008d2047a5652c9f9732359ee7248b29"]
def SliceU8.Insts.CoreOpsIndexIndexMutspecialized_Type_57510f1564d005eda0c45028821c0f658cf9a616f9dbf382cc9e92345d79bf26.index_mut : Slice Std.U8 →
    core.ops.range.RangeTo.specialized_Type_57510f1564d005eda0c45028821c0f658cf9a616f9dbf382cc9e92345d79bf26
    → Result ((Slice Std.U8) × (Slice Std.U8 → Slice Std.U8)) :=
  fun value range => Aeneas.Std.core.slice.index.SliceIndexRangeToUsizeSlice.index_mut {«end»:=range.«end»} value

/-- [core::slice::index::{impl core::ops::index::IndexMut<usize> for [u32]}::index_mut::specialized_Fun_7fafd2428e957c5da610df72acaf01b949860381b77858a3aff4e83dfd4b4ce2]:
    Source: '/rustc/library/core/src/slice/index.rs', lines 31:4-31:55
    Name pattern: [core::slice::index::{core::ops::index::IndexMut<[u32], usize>}::index_mut::specialized_Fun_7fafd2428e957c5da610df72acaf01b949860381b77858a3aff4e83dfd4b4ce2]
    Visibility: public -/
@[rust_fun
  "core::slice::index::{core::ops::index::IndexMut<[u32], usize>}::index_mut::specialized_Fun_7fafd2428e957c5da610df72acaf01b949860381b77858a3aff4e83dfd4b4ce2"]
def SliceU32.Insts.CoreOpsIndexIndexMutUsize.index_mut : Slice Std.U32 → Std.Usize → Result (Std.U32 × (Std.U32 → Slice
    Std.U32)) :=
  fun value index => Aeneas.Std.Slice.index_mut_usize value index

/-- [core::slice::{[u8]}::copy_from_slice::specialized_Fun_de5dde34cbd33edaf3624e3c58214b7fb7817a8aa46a83400e14a525efab8db3]:
    Source: '/rustc/library/core/src/slice/mod.rs', lines 4339:4-4341:16
    Name pattern: [core::slice::{[u8]}::copy_from_slice::specialized_Fun_de5dde34cbd33edaf3624e3c58214b7fb7817a8aa46a83400e14a525efab8db3]
    Visibility: public -/
@[rust_fun
  "core::slice::{[u8]}::copy_from_slice::specialized_Fun_de5dde34cbd33edaf3624e3c58214b7fb7817a8aa46a83400e14a525efab8db3"]
def core.slice.SliceU8.copy_from_slice.specialized_Fun_de5dde34cbd33edaf3624e3c58214b7fb7817a8aa46a83400e14a525efab8db3 : Slice Std.U8 → Slice Std.U8 → Result (Slice Std.U8) :=
  fun destination source => Aeneas.Std.core.slice.Slice.copy_from_slice Aeneas.Std.core.marker.CopyU8 destination source

/-- [hybrid_array::{hybrid_array::Array::specialized_Type_161f3369373d19cc76d29c248ae929c7343925f69236372b9c01f1e0e765ebda}::as_mut_slice::specialized_Fun_92e15419eb4ab248e70cfac0ace5adeb794c3fb21e20839a50befaa7b93576c2]:
    Source: '/Users/izzy/repos/tls-mpc/.deps/libsignal-vendor/hybrid-array-0.4.13/src/lib.rs', lines 185:4-185:52
    Name pattern: [hybrid_array::{hybrid_array::Array::specialized_Type_161f3369373d19cc76d29c248ae929c7343925f69236372b9c01f1e0e765ebda}::as_mut_slice::specialized_Fun_92e15419eb4ab248e70cfac0ace5adeb794c3fb21e20839a50befaa7b93576c2]
    Visibility: public -/
@[rust_fun
  "hybrid_array::{hybrid_array::Array::specialized_Type_161f3369373d19cc76d29c248ae929c7343925f69236372b9c01f1e0e765ebda}::as_mut_slice::specialized_Fun_92e15419eb4ab248e70cfac0ace5adeb794c3fb21e20839a50befaa7b93576c2"]
def hybrid_array.specialized_Type_161f3369373d19cc76d29c248ae929c7343925f69236372b9c01f1e0e765ebda.as_mut_slice.specialized_Fun_92e15419eb4ab248e70cfac0ace5adeb794c3fb21e20839a50befaa7b93576c2 : hybrid_array.Array.specialized_Type_161f3369373d19cc76d29c248ae929c7343925f69236372b9c01f1e0e765ebda
    → Result ((Slice Std.U8) × (Slice Std.U8 →
    hybrid_array.Array.specialized_Type_161f3369373d19cc76d29c248ae929c7343925f69236372b9c01f1e0e765ebda)) :=
  fun value => .ok (Aeneas.Std.Array.to_slice_mut value)

/-- [hybrid_array::{hybrid_array::Array::specialized_Type_ac20e7cfd6e9045f78d2db26067e6dbdbd9c399b9ec01bd6170d2d24f84de1ea}::as_slice::specialized_Fun_c158bfde138f40ff0fdc402f7611c9cc0cb4edd06f868a8b85a3162b880b2f10]:
    Source: '/Users/izzy/repos/tls-mpc/.deps/libsignal-vendor/hybrid-array-0.4.13/src/lib.rs', lines 177:4-177:40
    Name pattern: [hybrid_array::{hybrid_array::Array::specialized_Type_ac20e7cfd6e9045f78d2db26067e6dbdbd9c399b9ec01bd6170d2d24f84de1ea}::as_slice::specialized_Fun_c158bfde138f40ff0fdc402f7611c9cc0cb4edd06f868a8b85a3162b880b2f10]
    Visibility: public -/
@[rust_fun
  "hybrid_array::{hybrid_array::Array::specialized_Type_ac20e7cfd6e9045f78d2db26067e6dbdbd9c399b9ec01bd6170d2d24f84de1ea}::as_slice::specialized_Fun_c158bfde138f40ff0fdc402f7611c9cc0cb4edd06f868a8b85a3162b880b2f10"]
def hybrid_array.specialized_Type_ac20e7cfd6e9045f78d2db26067e6dbdbd9c399b9ec01bd6170d2d24f84de1ea.as_slice.specialized_Fun_c158bfde138f40ff0fdc402f7611c9cc0cb4edd06f868a8b85a3162b880b2f10 : hybrid_array.Array.specialized_Type_ac20e7cfd6e9045f78d2db26067e6dbdbd9c399b9ec01bd6170d2d24f84de1ea
    → Result (Slice Std.U32) :=
  fun value => .ok (Aeneas.Std.Array.to_slice value)

/-- [hybrid_array::{impl core::default::Default for hybrid_array::Array::specialized_Type_161f3369373d19cc76d29c248ae929c7343925f69236372b9c01f1e0e765ebda}::default::specialized_Fun_ce6eb92cb607c99ec9e93d56a8a34fc3097d36d5f8ca2d955e76eb080738e6a8]:
    Source: '/Users/izzy/repos/tls-mpc/.deps/libsignal-vendor/hybrid-array-0.4.13/src/lib.rs', lines 713:4-713:24
    Name pattern: [hybrid_array::{core::default::Default<hybrid_array::Array::specialized_Type_161f3369373d19cc76d29c248ae929c7343925f69236372b9c01f1e0e765ebda>}::default::specialized_Fun_ce6eb92cb607c99ec9e93d56a8a34fc3097d36d5f8ca2d955e76eb080738e6a8]
    Visibility: public -/
@[rust_fun
  "hybrid_array::{core::default::Default<hybrid_array::Array::specialized_Type_161f3369373d19cc76d29c248ae929c7343925f69236372b9c01f1e0e765ebda>}::default::specialized_Fun_ce6eb92cb607c99ec9e93d56a8a34fc3097d36d5f8ca2d955e76eb080738e6a8"]
def hybrid_array.Array.specialized_Type_161f3369373d19cc76d29c248ae929c7343925f69236372b9c01f1e0e765ebda.Insts.CoreDefaultDefault.default : Result
    hybrid_array.Array.specialized_Type_161f3369373d19cc76d29c248ae929c7343925f69236372b9c01f1e0e765ebda :=
  Aeneas.Std.core.default.DefaultArray.default (16#usize) Aeneas.Std.core.default.DefaultU8

/-- [hybrid_array::{hybrid_array::Array::specialized_Type_ac20e7cfd6e9045f78d2db26067e6dbdbd9c399b9ec01bd6170d2d24f84de1ea}::as_mut_slice::specialized_Fun_825ccce93a368e2609ce7b14475e48391b584346b5d9ba42bbabfbad5658ca03]:
    Source: '/Users/izzy/repos/tls-mpc/.deps/libsignal-vendor/hybrid-array-0.4.13/src/lib.rs', lines 185:4-185:52
    Name pattern: [hybrid_array::{hybrid_array::Array::specialized_Type_ac20e7cfd6e9045f78d2db26067e6dbdbd9c399b9ec01bd6170d2d24f84de1ea}::as_mut_slice::specialized_Fun_825ccce93a368e2609ce7b14475e48391b584346b5d9ba42bbabfbad5658ca03]
    Visibility: public -/
@[rust_fun
  "hybrid_array::{hybrid_array::Array::specialized_Type_ac20e7cfd6e9045f78d2db26067e6dbdbd9c399b9ec01bd6170d2d24f84de1ea}::as_mut_slice::specialized_Fun_825ccce93a368e2609ce7b14475e48391b584346b5d9ba42bbabfbad5658ca03"]
def hybrid_array.specialized_Type_ac20e7cfd6e9045f78d2db26067e6dbdbd9c399b9ec01bd6170d2d24f84de1ea.as_mut_slice.specialized_Fun_825ccce93a368e2609ce7b14475e48391b584346b5d9ba42bbabfbad5658ca03 : hybrid_array.Array.specialized_Type_ac20e7cfd6e9045f78d2db26067e6dbdbd9c399b9ec01bd6170d2d24f84de1ea
    → Result ((Slice Std.U32) × (Slice Std.U32 →
    hybrid_array.Array.specialized_Type_ac20e7cfd6e9045f78d2db26067e6dbdbd9c399b9ec01bd6170d2d24f84de1ea)) :=
  fun value => .ok (Aeneas.Std.Array.to_slice_mut value)

/-- [hybrid_array::{hybrid_array::Array::specialized_Type_161f3369373d19cc76d29c248ae929c7343925f69236372b9c01f1e0e765ebda}::as_slice::specialized_Fun_3b6f9f295dd0c583b3184c6ef668e3000914f98b988ca1fec01a596b182e5cf5]:
    Source: '/Users/izzy/repos/tls-mpc/.deps/libsignal-vendor/hybrid-array-0.4.13/src/lib.rs', lines 177:4-177:40
    Name pattern: [hybrid_array::{hybrid_array::Array::specialized_Type_161f3369373d19cc76d29c248ae929c7343925f69236372b9c01f1e0e765ebda}::as_slice::specialized_Fun_3b6f9f295dd0c583b3184c6ef668e3000914f98b988ca1fec01a596b182e5cf5]
    Visibility: public -/
@[rust_fun
  "hybrid_array::{hybrid_array::Array::specialized_Type_161f3369373d19cc76d29c248ae929c7343925f69236372b9c01f1e0e765ebda}::as_slice::specialized_Fun_3b6f9f295dd0c583b3184c6ef668e3000914f98b988ca1fec01a596b182e5cf5"]
def hybrid_array.specialized_Type_161f3369373d19cc76d29c248ae929c7343925f69236372b9c01f1e0e765ebda.as_slice.specialized_Fun_3b6f9f295dd0c583b3184c6ef668e3000914f98b988ca1fec01a596b182e5cf5 : hybrid_array.Array.specialized_Type_161f3369373d19cc76d29c248ae929c7343925f69236372b9c01f1e0e765ebda
    → Result (Slice Std.U8) :=
  fun value => .ok (Aeneas.Std.Array.to_slice value)

/-- [hybrid_array::{impl core::default::Default for hybrid_array::Array::specialized_Type_ac20e7cfd6e9045f78d2db26067e6dbdbd9c399b9ec01bd6170d2d24f84de1ea}::default::specialized_Fun_e1f667b9c0db4d9adc47665904820f50ad8df54e4d804f0447a9f28bde195077]:
    Source: '/Users/izzy/repos/tls-mpc/.deps/libsignal-vendor/hybrid-array-0.4.13/src/lib.rs', lines 713:4-713:24
    Name pattern: [hybrid_array::{core::default::Default<hybrid_array::Array::specialized_Type_ac20e7cfd6e9045f78d2db26067e6dbdbd9c399b9ec01bd6170d2d24f84de1ea>}::default::specialized_Fun_e1f667b9c0db4d9adc47665904820f50ad8df54e4d804f0447a9f28bde195077]
    Visibility: public -/
@[rust_fun
  "hybrid_array::{core::default::Default<hybrid_array::Array::specialized_Type_ac20e7cfd6e9045f78d2db26067e6dbdbd9c399b9ec01bd6170d2d24f84de1ea>}::default::specialized_Fun_e1f667b9c0db4d9adc47665904820f50ad8df54e4d804f0447a9f28bde195077"]
def hybrid_array.Array.specialized_Type_ac20e7cfd6e9045f78d2db26067e6dbdbd9c399b9ec01bd6170d2d24f84de1ea.Insts.CoreDefaultDefault.default : Result
    hybrid_array.Array.specialized_Type_ac20e7cfd6e9045f78d2db26067e6dbdbd9c399b9ec01bd6170d2d24f84de1ea :=
  Aeneas.Std.core.default.DefaultArray.default (4#usize) Aeneas.Std.core.default.DefaultU32

end CtrStateV1
