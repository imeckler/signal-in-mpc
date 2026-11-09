-- AUTHORED actual-leaf forwarding + six explicit Std content bindings.
-- [aes]: external functions.
-- This is a template file: rename it to "FunsExternal.lean" and fill the holes.
import Aeneas
import AesCtrBlockWork.Generated.EncryptNamedV1.Types
import LibSignalReference.Generated.AesLayout.Funs
import LibSignalReference.Generated.AesSubBytes.Funs
import LibSignalReference.Generated.AesMix.Funs
import LibSignalReference.Generated.AesMixPhases.Funs
import LibSignalReference.Generated.AesShift.Funs
import AesCtrBlockWork.Generated.InvBitsliceNamedV1.Funs
import AesCtrBlockWork.ZipModelV1.ActualRoundKey
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048
namespace RustCryptoAesCtrBlock

/-- [core::array::{impl core::ops::index::Index<core::ops::range::RangeTo::specialized_Type_57510f1564d005eda0c45028821c0f658cf9a616f9dbf382cc9e92345d79bf26> for [u64; 120usize]}::index::specialized_Fun_1fe7038bb3f8763883bd08f76dbdeee5d60195d77b43ecac3c683756114823fc]:
    Source: '/rustc/library/core/src/array/mod.rs', lines 390:4-390:46
    Name pattern: [core::array::{core::ops::index::Index<[u64; 120], core::ops::range::RangeTo::specialized_Type_57510f1564d005eda0c45028821c0f658cf9a616f9dbf382cc9e92345d79bf26>}::index::specialized_Fun_1fe7038bb3f8763883bd08f76dbdeee5d60195d77b43ecac3c683756114823fc]
    Visibility: public -/
@[rust_fun
  "core::array::{core::ops::index::Index<[u64; 120], core::ops::range::RangeTo::specialized_Type_57510f1564d005eda0c45028821c0f658cf9a616f9dbf382cc9e92345d79bf26>}::index::specialized_Fun_1fe7038bb3f8763883bd08f76dbdeee5d60195d77b43ecac3c683756114823fc"]
def ArrayU64120.Insts.CoreOpsIndexIndexspecialized_Type_57510f1564d005eda0c45028821c0f658cf9a616f9dbf382cc9e92345d79bf26.index : Array Std.U64 120#usize →
    core.ops.range.RangeTo.specialized_Type_57510f1564d005eda0c45028821c0f658cf9a616f9dbf382cc9e92345d79bf26
    → Result (Slice Std.U64) :=
  fun value range => Aeneas.Std.core.slice.index.SliceIndexRangeToUsizeSlice.index {«end»:=range.end} value.to_slice

/-- [core::array::{impl core::ops::index::Index<core::ops::range::Range::specialized_Type_a6d41e09652f1286a20c9e5d6cdaa143f56a848c0ded3779accf5fbb4661efb9> for [u64; 120usize]}::index::specialized_Fun_5eea0a99dbf91cbb79e1d60228b2c33f23014ba17fba71965ee5d6db1896cbef]:
    Source: '/rustc/library/core/src/array/mod.rs', lines 390:4-390:46
    Name pattern: [core::array::{core::ops::index::Index<[u64; 120], core::ops::range::Range::specialized_Type_a6d41e09652f1286a20c9e5d6cdaa143f56a848c0ded3779accf5fbb4661efb9>}::index::specialized_Fun_5eea0a99dbf91cbb79e1d60228b2c33f23014ba17fba71965ee5d6db1896cbef]
    Visibility: public -/
@[rust_fun
  "core::array::{core::ops::index::Index<[u64; 120], core::ops::range::Range::specialized_Type_a6d41e09652f1286a20c9e5d6cdaa143f56a848c0ded3779accf5fbb4661efb9>}::index::specialized_Fun_5eea0a99dbf91cbb79e1d60228b2c33f23014ba17fba71965ee5d6db1896cbef"]
def ArrayU64120.Insts.CoreOpsIndexIndexspecialized_Type_a6d41e09652f1286a20c9e5d6cdaa143f56a848c0ded3779accf5fbb4661efb9.index : Array Std.U64 120#usize →
    core.ops.range.Range.specialized_Type_a6d41e09652f1286a20c9e5d6cdaa143f56a848c0ded3779accf5fbb4661efb9
    → Result (Slice Std.U64) :=
  fun value range => Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.index {start:=range.start,«end»:=range.end} value.to_slice

/-- [core::array::{impl core::ops::index::Index<core::ops::range::RangeFrom::specialized_Type_d1f2f41ce9b6a4bab41ab00dc2d7f45668cf5cd166e8302372ae9482af4f16f6> for [u64; 120usize]}::index::specialized_Fun_49df35947667986cbcb6fe4b78682ccba68372fe8d303d8bcbabc9ad61e280bc]:
    Source: '/rustc/library/core/src/array/mod.rs', lines 390:4-390:46
    Name pattern: [core::array::{core::ops::index::Index<[u64; 120], core::ops::range::RangeFrom::specialized_Type_d1f2f41ce9b6a4bab41ab00dc2d7f45668cf5cd166e8302372ae9482af4f16f6>}::index::specialized_Fun_49df35947667986cbcb6fe4b78682ccba68372fe8d303d8bcbabc9ad61e280bc]
    Visibility: public -/
@[rust_fun
  "core::array::{core::ops::index::Index<[u64; 120], core::ops::range::RangeFrom::specialized_Type_d1f2f41ce9b6a4bab41ab00dc2d7f45668cf5cd166e8302372ae9482af4f16f6>}::index::specialized_Fun_49df35947667986cbcb6fe4b78682ccba68372fe8d303d8bcbabc9ad61e280bc"]
def ArrayU64120.Insts.CoreOpsIndexIndexspecialized_Type_d1f2f41ce9b6a4bab41ab00dc2d7f45668cf5cd166e8302372ae9482af4f16f6.index : Array Std.U64 120#usize →
    core.ops.range.RangeFrom.specialized_Type_d1f2f41ce9b6a4bab41ab00dc2d7f45668cf5cd166e8302372ae9482af4f16f6
    → Result (Slice Std.U64) :=
  fun value range => Aeneas.Std.core.slice.index.SliceIndexRangeFromUsizeSlice.index {start:=range.start} value.to_slice

/-- [core::array::{impl core::default::Default for [u64; 8usize]}::default::specialized_Fun_2553c130d6763c3f53fe67d98dcc3784aa575d44fe2b62bb56dcc71f850298f4]:
    Source: '/rustc/library/core/src/array/mod.rs', lines 522:12-522:35
    Name pattern: [core::array::{core::default::Default<[u64; 8]>}::default::specialized_Fun_2553c130d6763c3f53fe67d98dcc3784aa575d44fe2b62bb56dcc71f850298f4]
    Visibility: public -/
@[rust_fun
  "core::array::{core::default::Default<[u64; 8]>}::default::specialized_Fun_2553c130d6763c3f53fe67d98dcc3784aa575d44fe2b62bb56dcc71f850298f4"]
def ArrayU648.Insts.CoreDefaultDefault.default : Result (Array Std.U64 8#usize) :=
  Aeneas.Std.core.default.DefaultArray.default (8#usize) Aeneas.Std.core.default.DefaultU64

/-- [hybrid_array::{impl core::ops::deref::Deref for hybrid_array::Array::specialized_Type_f6d0079c9d47818b2c760c13dc530abd0fcf2330bbf625eeaa753c4e448e7d5f}::deref::specialized_Fun_8ef60c85381a109e93556d6770eab769443da355cc2e73b93828751831677185]:
    Source: '/Users/izzy/repos/tls-mpc/.deps/libsignal-vendor/hybrid-array-0.4.13/src/lib.rs', lines 725:4-725:27
    Name pattern: [hybrid_array::{core::ops::deref::Deref<hybrid_array::Array::specialized_Type_f6d0079c9d47818b2c760c13dc530abd0fcf2330bbf625eeaa753c4e448e7d5f>}::deref::specialized_Fun_8ef60c85381a109e93556d6770eab769443da355cc2e73b93828751831677185]
    Visibility: public -/
@[rust_fun
  "hybrid_array::{core::ops::deref::Deref<hybrid_array::Array::specialized_Type_f6d0079c9d47818b2c760c13dc530abd0fcf2330bbf625eeaa753c4e448e7d5f>}::deref::specialized_Fun_8ef60c85381a109e93556d6770eab769443da355cc2e73b93828751831677185"]
def hybrid_array.Array.specialized_Type_f6d0079c9d47818b2c760c13dc530abd0fcf2330bbf625eeaa753c4e448e7d5f.Insts.CoreOpsDerefDeref.deref : hybrid_array.Array.specialized_Type_f6d0079c9d47818b2c760c13dc530abd0fcf2330bbf625eeaa753c4e448e7d5f
    → Result (Slice Std.U8) :=
  fun value=>.ok value.to_slice

/-- [hybrid_array::{impl core::ops::index::Index<usize> for hybrid_array::Array::specialized_Type_466e03121b73c7d435361c7adc904649fbf81c760e593c61b65a8532a101fdf5}::index::specialized_Fun_de0cd6cbb777bad4f765f3fb4ff6b85722ab7abc324997a95c4926aec2f8f14d]:
    Source: '/Users/izzy/repos/tls-mpc/.deps/libsignal-vendor/hybrid-array-0.4.13/src/lib.rs', lines 872:4-872:46
    Name pattern: [hybrid_array::{core::ops::index::Index<hybrid_array::Array::specialized_Type_466e03121b73c7d435361c7adc904649fbf81c760e593c61b65a8532a101fdf5, usize>}::index::specialized_Fun_de0cd6cbb777bad4f765f3fb4ff6b85722ab7abc324997a95c4926aec2f8f14d]
    Visibility: public -/
@[rust_fun
  "hybrid_array::{core::ops::index::Index<hybrid_array::Array::specialized_Type_466e03121b73c7d435361c7adc904649fbf81c760e593c61b65a8532a101fdf5, usize>}::index::specialized_Fun_de0cd6cbb777bad4f765f3fb4ff6b85722ab7abc324997a95c4926aec2f8f14d"]
def hybrid_array.Array.specialized_Type_466e03121b73c7d435361c7adc904649fbf81c760e593c61b65a8532a101fdf5.Insts.CoreOpsIndexIndexUsize.index : hybrid_array.Array.specialized_Type_466e03121b73c7d435361c7adc904649fbf81c760e593c61b65a8532a101fdf5
    → Std.Usize → Result
    hybrid_array.Array.specialized_Type_f6d0079c9d47818b2c760c13dc530abd0fcf2330bbf625eeaa753c4e448e7d5f :=
  Aeneas.Std.Array.index_usize

/-- [aes::soft::fixslice::add_round_key]:
    Source: 'src/soft/fixslice64.rs', lines 1362:0-1367:1 -/
def soft.fixslice.add_round_key : Array Std.U64 8#usize → Slice Std.U64 → Result (Array Std.U64 8#usize) :=
  RustCryptoAesZipDiagnostic.soft.fixslice.add_round_key

/-- [aes::soft::fixslice::inv_bitslice]:
    Source: 'src/soft/fixslice64.rs', lines 1270:0-1345:1 -/
def soft.fixslice.inv_bitslice : Slice Std.U64 → Result
    hybrid_array.Array.specialized_Type_466e03121b73c7d435361c7adc904649fbf81c760e593c61b65a8532a101fdf5 :=
  RustCryptoAesCtrInverse.soft.fixslice.inv_bitslice

/-- [aes::soft::fixslice::bitslice]:
    Source: 'src/soft/fixslice64.rs', lines 1193:0-1267:1 -/
def soft.fixslice.bitslice : Slice Std.U64 → Slice Std.U8 → Slice Std.U8 → Slice Std.U8 → Slice
    Std.U8 → Result (Slice Std.U64) :=
  RustCryptoAesLayout.soft.fixslice.bitslice

/-- [aes::soft::fixslice::shift_rows_2]:
    Source: 'src/soft/fixslice64.rs', lines 1140:0-1145:1 -/
def soft.fixslice.shift_rows_2 : Slice Std.U64 → Result (Slice Std.U64) :=
  RustCryptoAesLinear.soft.fixslice.shift_rows_2

/-- [aes::soft::fixslice::mix_columns_0]:
    Source: 'src/soft/fixslice64.rs', lines 993:8-1025:9 -/
def soft.fixslice.mix_columns_0 : Array Std.U64 8#usize → Result (Array Std.U64 8#usize) :=
  RustCryptoAesLinear.soft.fixslice.mix_columns_0

/-- [aes::soft::fixslice::mix_columns_3]:
    Source: 'src/soft/fixslice64.rs', lines 993:8-1025:9 -/
def soft.fixslice.mix_columns_3 : Array Std.U64 8#usize → Result (Array Std.U64 8#usize) :=
  RustCryptoAesRemainingLinear.soft.fixslice.mix_columns_3

/-- [aes::soft::fixslice::mix_columns_2]:
    Source: 'src/soft/fixslice64.rs', lines 993:8-1025:9 -/
def soft.fixslice.mix_columns_2 : Array Std.U64 8#usize → Result (Array Std.U64 8#usize) :=
  RustCryptoAesRemainingLinear.soft.fixslice.mix_columns_2

/-- [aes::soft::fixslice::mix_columns_1]:
    Source: 'src/soft/fixslice64.rs', lines 993:8-1025:9 -/
def soft.fixslice.mix_columns_1 : Array Std.U64 8#usize → Result (Array Std.U64 8#usize) :=
  RustCryptoAesRemainingLinear.soft.fixslice.mix_columns_1

/-- [aes::soft::fixslice::sub_bytes]:
    Source: 'src/soft/fixslice64.rs', lines 800:0-969:1 -/
def soft.fixslice.sub_bytes : Slice Std.U64 → Result (Slice Std.U64) :=
  RustCryptoAesSubBytes.soft.fixslice.sub_bytes

end RustCryptoAesCtrBlock
