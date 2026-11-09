import AesCtrBlockWork.EncryptBoundV1.Funs
namespace LibSignalReference.Candidate.AesActualBindings

theorem round_key : RustCryptoAesCtrBlock.soft.fixslice.add_round_key =
 RustCryptoAesZipDiagnostic.soft.fixslice.add_round_key := rfl
theorem inverse : RustCryptoAesCtrBlock.soft.fixslice.inv_bitslice =
 RustCryptoAesCtrInverse.soft.fixslice.inv_bitslice := rfl
theorem forward : RustCryptoAesCtrBlock.soft.fixslice.bitslice =
 RustCryptoAesLayout.soft.fixslice.bitslice := rfl
theorem substitution : RustCryptoAesCtrBlock.soft.fixslice.sub_bytes =
 RustCryptoAesSubBytes.soft.fixslice.sub_bytes := rfl
theorem shift : RustCryptoAesCtrBlock.soft.fixslice.shift_rows_2 =
 RustCryptoAesLinear.soft.fixslice.shift_rows_2 := rfl
theorem mix0 : RustCryptoAesCtrBlock.soft.fixslice.mix_columns_0 =
 RustCryptoAesLinear.soft.fixslice.mix_columns_0 := rfl
theorem mix1 : RustCryptoAesCtrBlock.soft.fixslice.mix_columns_1 =
 RustCryptoAesRemainingLinear.soft.fixslice.mix_columns_1 := rfl
theorem mix2 : RustCryptoAesCtrBlock.soft.fixslice.mix_columns_2 =
 RustCryptoAesRemainingLinear.soft.fixslice.mix_columns_2 := rfl
theorem mix3 : RustCryptoAesCtrBlock.soft.fixslice.mix_columns_3 =
 RustCryptoAesRemainingLinear.soft.fixslice.mix_columns_3 := rfl
end LibSignalReference.Candidate.AesActualBindings
