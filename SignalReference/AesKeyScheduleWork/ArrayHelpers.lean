import AesKeyScheduleWork.ArrayWindows
import AesKeyScheduleWork.CopyBridge
import AesKeyScheduleLeavesWork.Nots
import AesKeyScheduleLeavesWork.InverseShift

namespace LibSignalReference.Candidate.AesKeySchedule

open Aeneas Aeneas.Std
open RustCryptoAesKeySchedule
open TlsMpc
open LibSignalReference.Proofs.AesKeyScheduleLeaves

set_option maxHeartbeats 2000000

def copyArray (words : Array U64 size) (source : Usize) : Result (Array U64 size) := do
  let (part, back) ← lift (Array.to_slice_mut words)
  let result ← soft.fixslice.memshift32 part source
  .ok (back result)

theorem copyArray_spec (words : Array U64 size) (source : Usize)
    (ha : source.val % 8 = 0) (hs : source.val + 16 ≤ size.val) :
    ∃ result, copyArray words source = .ok result ∧
      result.val.map UScalar.bv = Signal.AesKeyCopy.copyBackward 0 source.val
        (source.val + 8) 8 (words.val.map UScalar.bv) := by
  let copied := AesKeyCopy.copyBackward source.val (source.val + 8) 8 words.to_slice
  have hsize : source.val + 16 ≤ words.to_slice.length := by simpa [Array.to_slice, Slice.length] using hs
  have hl : copied.val.length = size.val := by
    change copied.length = size.val
    simp [copied, AesKeyCopy.copyBackward_length, Array.to_slice, Slice.length]
  refine ⟨Array.from_slice words copied, ?_, ?_⟩
  · with_unfolding_all simp [copyArray, Array.to_slice_mut, lift,
      AesKeyCopy.memshift32_spec source words.to_slice ha hsize, copied]
  · rw [Array.from_slice_val _ _ hl, AesKeyCopy.copyBackward_bv]
    rfl

def columnsArray (words : Array U64 size) (offset distance : Usize) (rotation : U32) :
    Result (Array U64 size) := do
  let (part, back) ← lift (Array.to_slice_mut words)
  let result ← soft.fixslice.xor_columns part offset distance rotation
  .ok (back result)

theorem columnsArray_spec (words : Array U64 size) (offset distance : Usize) (rotation : U32)
    (hd : distance.val ≤ offset.val) (hs : offset.val + 8 ≤ size.val) :
    ∃ result, columnsArray words offset distance rotation = .ok result ∧
      result.val.map UScalar.bv = Signal.AesKeyColumns.run 0
        (Signal.AesKeyColumns.column Signal.AesKeyColumns.concrete rotation.val)
        offset.val distance.val 0 8 (words.val.map UScalar.bv) := by
  let updated := AesKeyColumns.run offset.val distance.val rotation.val 0 8 words.to_slice
  have hsize : offset.val + 8 ≤ words.to_slice.length := by simpa [Array.to_slice, Slice.length] using hs
  have hl : updated.val.length = size.val := by
    change updated.length = size.val
    simp [updated, AesKeyColumns.run_length, Array.to_slice, Slice.length]
  refine ⟨Array.from_slice words updated, ?_, ?_⟩
  · with_unfolding_all simp [columnsArray, Array.to_slice_mut, lift,
      AesKeyColumns.xor_columns_spec offset distance rotation words.to_slice hd hsize, updated]
  · rw [Array.from_slice_val _ _ hl, AesKeyColumns.run_bv]
    rfl

theorem add_constant_slice (part : Slice U64) (round : Usize)
    (hl : part.length = 8) (hr : round.val < 8) :
    ∃ result, soft.fixslice.add_round_constant_bit part round = .ok result ∧
      result.length = 8 ∧ result.val.map UScalar.bv =
        Signal.AesKeySchedule.addConstant Signal.AesKeySchedule.concrete 0 round.val
          (part.val.map UScalar.bv) := by
  let result := part.setAtNat round.val
    ((part.val[round.val]?.getD 0#u64) ^^^ 4026531840#u64)
  have hb : round.val < part.val.length := by change _ < part.length; omega
  refine ⟨result, ?_, ?_, ?_⟩
  · simp [soft.fixslice.add_round_constant_bit, Slice.index_usize, Slice.update,
      lift, result, Slice.setAtNat, List.getElem?_eq_getElem hb]
  · simp [result, Slice.length, ← hl]
  · simp [result, Slice.setAtNat, List.map_set, Signal.AesKeySchedule.addConstant,
      Signal.AesKeySchedule.concrete, List.getElem?_map, List.getElem?_eq_getElem hb]

def substituteArray (words : Array U64 size) (start finish : Usize) : Result (Array U64 size) := do
  let intermediate ← applyWindow words start finish soft.fixslice.sub_bytes
  applyWindow intermediate start finish soft.fixslice.sub_bytes_nots

theorem substituteArray_spec (words : Array U64 size) (start finish : Usize)
    (he : finish.val = start.val + 8) (hs : finish.val ≤ size.val) :
    ∃ result,
      substituteArray words start finish = .ok result ∧
      result.val.map UScalar.bv = Signal.AesKeySchedule.window
        Signal.AesKeySchedule.concrete.substitute start.val (words.val.map UScalar.bv) := by
  rw [substituteArray, applyWindow_compose words start finish he hs _ _ sub_bytes_preserves_shape nots_preserves_shape]
  apply applyWindow_spec words start finish he hs
  intro part hp
  obtain ⟨result, hr, hv⟩ := restored_slice part hp
  refine ⟨result, hr, ?_, hv⟩
  have heq := congrArg List.length hv
  simpa [TlsMpc.AesSbox.circuit, TlsMpc.AesSbox.outputIndices] using heq

@[step] theorem copyArray_step (words : Array U64 size) (source : Usize)
    (ha : source.val % 8 = 0) (hs : source.val + 16 ≤ size.val) :
    copyArray words source ⦃ result => result.val.map UScalar.bv =
      Signal.AesKeyCopy.copyBackward 0 source.val (source.val + 8) 8 (words.val.map UScalar.bv) ⦄ := by
  obtain ⟨result, hr, hv⟩ := copyArray_spec words source ha hs
  simp [hr, hv]

@[step] theorem columnsArray_step (words : Array U64 size) (offset distance : Usize) (rotation : U32)
    (hd : distance.val ≤ offset.val) (hs : offset.val + 8 ≤ size.val) :
    columnsArray words offset distance rotation ⦃ result => result.val.map UScalar.bv =
      Signal.AesKeyColumns.run 0 (Signal.AesKeyColumns.column Signal.AesKeyColumns.concrete rotation.val)
        offset.val distance.val 0 8 (words.val.map UScalar.bv) ⦄ := by
  obtain ⟨result, hr, hv⟩ := columnsArray_spec words offset distance rotation hd hs
  simp [hr, hv]

@[step] theorem substituteArray_step (words : Array U64 size) (start finish : Usize)
    (he : finish.val = start.val + 8) (hs : finish.val ≤ size.val) :
    substituteArray words start finish ⦃ result => result.val.map UScalar.bv =
      Signal.AesKeySchedule.window Signal.AesKeySchedule.concrete.substitute start.val
        (words.val.map UScalar.bv) ⦄ := by
  obtain ⟨result, hr, hv⟩ := substituteArray_spec words start finish he hs
  simp [hr, hv]

@[step] theorem addConstantArray_step (words : Array U64 size) (start finish round : Usize)
    (he : finish.val = start.val + 8) (hs : finish.val ≤ size.val) (hr : round.val < 8) :
    applyWindow words start finish (fun part => soft.fixslice.add_round_constant_bit part round)
      ⦃ result => result.val.map UScalar.bv = Signal.AesKeySchedule.window
        (Signal.AesKeySchedule.addConstant Signal.AesKeySchedule.concrete 0 round.val)
        start.val (words.val.map UScalar.bv) ⦄ := by
  obtain ⟨result, hout, hv⟩ := applyWindow_spec words start finish he hs _ _
    (fun part hpart => add_constant_slice part round hpart hr)
  simp [hout, hv]

end LibSignalReference.Candidate.AesKeySchedule
