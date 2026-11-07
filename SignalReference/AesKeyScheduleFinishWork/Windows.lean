import AesKeyScheduleWork.ArrayHelpers

namespace LibSignalReference.Candidate.AesKeyScheduleFinish

open Aeneas Aeneas.Std
open RustCryptoAesKeySchedule
open LibSignalReference.Candidate.AesKeySchedule
open LibSignalReference.Proofs.AesKeyScheduleLeaves
open TlsMpc.Signal.AesKeySchedule (concrete window restoreNots)

set_option maxHeartbeats 2000000

theorem inverse1Array_spec (words : Array U64 size) (start finish : Usize)
    (he : finish.val = start.val + 8) (hs : finish.val ≤ size.val) :
    ∃ result, applyWindow words start finish soft.fixslice.inv_shift_rows_1 = .ok result ∧
      result.val.map UScalar.bv = window (List.map concrete.inv1) start.val
        (words.val.map UScalar.bv) := by
  apply applyWindow_spec words start finish he hs
  intro part hp
  obtain ⟨result, hr, hv⟩ := inverse1_slice part hp
  refine ⟨result, hr, ?_, hv⟩
  have hl := congrArg List.length hv
  simpa only [List.length_map, show part.val.length = 8 from hp] using hl

theorem inverse2Array_spec (words : Array U64 size) (start finish : Usize)
    (he : finish.val = start.val + 8) (hs : finish.val ≤ size.val) :
    ∃ result, applyWindow words start finish soft.fixslice.inv_shift_rows_2 = .ok result ∧
      result.val.map UScalar.bv = window (List.map concrete.inv2) start.val
        (words.val.map UScalar.bv) := by
  apply applyWindow_spec words start finish he hs
  intro part hp
  obtain ⟨result, hr, hv⟩ := inverse2_slice part hp
  refine ⟨result, hr, ?_, hv⟩
  have hl := congrArg List.length hv
  simpa only [List.length_map, show part.val.length = 8 from hp] using hl

theorem inverse3Array_spec (words : Array U64 size) (start finish : Usize)
    (he : finish.val = start.val + 8) (hs : finish.val ≤ size.val) :
    ∃ result, applyWindow words start finish soft.fixslice.inv_shift_rows_3 = .ok result ∧
      result.val.map UScalar.bv = window (List.map concrete.inv3) start.val
        (words.val.map UScalar.bv) := by
  apply applyWindow_spec words start finish he hs
  intro part hp
  obtain ⟨result, hr, hv⟩ := inverse3_slice part hp
  refine ⟨result, hr, ?_, hv⟩
  have hl := congrArg List.length hv
  simpa only [List.length_map, show part.val.length = 8 from hp] using hl

theorem notsArray_spec (words : Array U64 size) (start finish : Usize)
    (he : finish.val = start.val + 8) (hs : finish.val ≤ size.val) :
    ∃ result, applyWindow words start finish soft.fixslice.sub_bytes_nots = .ok result ∧
      result.val.map UScalar.bv = window (restoreNots concrete 0) start.val
        (words.val.map UScalar.bv) := by
  apply applyWindow_spec words start finish he hs
  intro part hp
  obtain ⟨result, hr, hv⟩ := nots_slice part hp
  refine ⟨result, hr, ?_, hv⟩
  have hl := congrArg List.length hv
  simpa only [restoreNots, List.length_set, List.length_map,
    show part.val.length = 8 from hp] using hl

@[step] theorem inverse1Array_step (words : Array U64 size) (start finish : Usize)
    (he : finish.val = start.val + 8) (hs : finish.val ≤ size.val) :
    applyWindow words start finish soft.fixslice.inv_shift_rows_1
      ⦃ result => result.val.map UScalar.bv = window (List.map concrete.inv1) start.val
        (words.val.map UScalar.bv) ⦄ := by
  obtain ⟨result, hr, hv⟩ := inverse1Array_spec words start finish he hs
  simp [hr, hv]

@[step] theorem inverse2Array_step (words : Array U64 size) (start finish : Usize)
    (he : finish.val = start.val + 8) (hs : finish.val ≤ size.val) :
    applyWindow words start finish soft.fixslice.inv_shift_rows_2
      ⦃ result => result.val.map UScalar.bv = window (List.map concrete.inv2) start.val
        (words.val.map UScalar.bv) ⦄ := by
  obtain ⟨result, hr, hv⟩ := inverse2Array_spec words start finish he hs
  simp [hr, hv]

@[step] theorem inverse3Array_step (words : Array U64 size) (start finish : Usize)
    (he : finish.val = start.val + 8) (hs : finish.val ≤ size.val) :
    applyWindow words start finish soft.fixslice.inv_shift_rows_3
      ⦃ result => result.val.map UScalar.bv = window (List.map concrete.inv3) start.val
        (words.val.map UScalar.bv) ⦄ := by
  obtain ⟨result, hr, hv⟩ := inverse3Array_spec words start finish he hs
  simp [hr, hv]

@[step] theorem notsArray_step (words : Array U64 size) (start finish : Usize)
    (he : finish.val = start.val + 8) (hs : finish.val ≤ size.val) :
    applyWindow words start finish soft.fixslice.sub_bytes_nots
      ⦃ result => result.val.map UScalar.bv = window (restoreNots concrete 0) start.val
        (words.val.map UScalar.bv) ⦄ := by
  obtain ⟨result, hr, hv⟩ := notsArray_spec words start finish he hs
  simp [hr, hv]

end LibSignalReference.Candidate.AesKeyScheduleFinish
