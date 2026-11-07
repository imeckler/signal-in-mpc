import AesKeyScheduleWork.Generated.Funs
import LibSignalReference.Generated.AesSubBytes.Funs
import LibSignalReference.Generated.AesLayout.Funs
import LibSignalReference.Generated.AesShift.Funs

/-! These are equalities between actual Aeneas-generated definitions from the
same locked aes0.9.1 source, extracted through different selected call graphs.
They preserve full Result behavior, including invalid shapes and shifts. -/

namespace LibSignalReference.Proofs.AesKeyScheduleLeaves

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem sub_bytes_eq :
    RustCryptoAesKeySchedule.soft.fixslice.sub_bytes =
      RustCryptoAesSubBytes.soft.fixslice.sub_bytes := by rfl

theorem sub_bytes_nots_eq :
    RustCryptoAesKeySchedule.soft.fixslice.sub_bytes_nots =
      RustCryptoAesSubBytes.soft.fixslice.sub_bytes_nots := by rfl

theorem read_reordered_eq :
    RustCryptoAesKeySchedule.soft.fixslice.bitslice.read_reordered =
      RustCryptoAesLayout.soft.fixslice.bitslice.read_reordered := by rfl

theorem delta_swap2_eq :
    RustCryptoAesKeySchedule.soft.fixslice.delta_swap_2 =
      RustCryptoAesLayout.soft.fixslice.delta_swap_2 := by rfl

theorem bitslice_eq :
    RustCryptoAesKeySchedule.soft.fixslice.bitslice =
      RustCryptoAesLayout.soft.fixslice.bitslice := by rfl

theorem delta_swap1_eq :
    RustCryptoAesKeySchedule.soft.fixslice.delta_swap_1 =
      RustCryptoAesLinear.soft.fixslice.delta_swap_1 := by rfl

theorem shift1_eq :
    RustCryptoAesKeySchedule.soft.fixslice.shift_rows_1 =
      RustCryptoAesLinear.soft.fixslice.shift_rows_1 := by rfl

theorem shift2_eq :
    RustCryptoAesKeySchedule.soft.fixslice.shift_rows_2 =
      RustCryptoAesLinear.soft.fixslice.shift_rows_2 := by rfl

theorem shift3_eq :
    RustCryptoAesKeySchedule.soft.fixslice.shift_rows_3 =
      RustCryptoAesLinear.soft.fixslice.shift_rows_3 := by rfl

theorem inverse1_eq :
    RustCryptoAesKeySchedule.soft.fixslice.inv_shift_rows_1 =
      RustCryptoAesLinear.soft.fixslice.shift_rows_3 := by rfl

theorem inverse2_eq :
    RustCryptoAesKeySchedule.soft.fixslice.inv_shift_rows_2 =
      RustCryptoAesLinear.soft.fixslice.shift_rows_2 := by rfl

theorem inverse3_eq :
    RustCryptoAesKeySchedule.soft.fixslice.inv_shift_rows_3 =
      RustCryptoAesLinear.soft.fixslice.shift_rows_1 := by rfl

end LibSignalReference.Proofs.AesKeyScheduleLeaves
