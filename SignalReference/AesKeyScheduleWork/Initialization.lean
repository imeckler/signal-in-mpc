import AesKeyScheduleWork.ArrayHelpers
import LibSignalReference.Proofs.AesLayout
import TlsMpc.Signal.AesKeyInput

namespace LibSignalReference.Candidate.AesKeySchedule

open Aeneas Aeneas.Std
open RustCryptoAesKeySchedule
open TlsMpc.Signal.AesLayout
open LibSignalReference.Proofs.AesLayout
open LibSignalReference.Proofs.AesKeyScheduleLeaves

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def keyArray (key : Nat → U8) : Array U8 32#usize :=
  ⟨[key 0,key 1,key 2,key 3,key 4,key 5,key 6,key 7,
    key 8,key 9,key 10,key 11,key 12,key 13,key 14,key 15,
    key 16,key 17,key 18,key 19,key 20,key 21,key 22,key 23,
    key 24,key 25,key 26,key 27,key 28,key 29,key 30,key 31], by simp⟩

theorem keyArray_all (key : Array U8 32#usize) :
    keyArray (fun i => key.val[i]?.getD 0#u8) = key := by
  apply Subtype.ext
  have hk : key.val.length = 32 := by simpa using key.property
  change (List.range 32).map (fun i => key.val[i]?.getD 0#u8) = key.val
  apply List.ext_getElem
  · simp [hk]
  · intro index hleft hright
    simp only [List.getElem_map, List.getElem_range, List.getElem?_eq_getElem hright, Option.getD_some]

theorem key_first (key : Nat → U8) :
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice U8)) (keyArray key) ⟨16#usize⟩ =
      .ok (slice16 key) := by
  simp [core.array.Array.index, core.ops.index.IndexSlice, core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeToUsizeSlice, core.slice.index.SliceIndexRangeToUsizeSlice.index,
    keyArray, Array.to_slice, slice16, List.slice]

theorem key_second (key : Nat → U8) :
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeFromUsizeSlice U8)) (keyArray key) ⟨16#usize⟩ =
      .ok (slice16 (fun index => key (16 + index))) := by
  simp [core.array.Array.index, core.ops.index.IndexSlice, core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeFromUsizeSlice, core.slice.index.SliceIndexRangeFromUsizeSlice.index,
    keyArray, Array.to_slice, slice16, Slice.drop]

@[step] theorem bitslice_repeat_step (state : Slice U64) (key : Nat → U8) (hs : state.length = 8) :
    soft.fixslice.bitslice state (slice16 key) (slice16 key) (slice16 key) (slice16 key)
      ⦃ result => result = wordSlice (network (fun _ index => (key index).bv)) ⦄ := by
  obtain ⟨initial, rfl⟩ := slice_as_wordSlice state hs
  rw [bitslice_eq, bitslice_network (fun _ index => key index) initial]
  simp

/-- Proof-only factoring of the initial borrows in the actual entrypoint. -/
def initialState (key : Array U8 32#usize) : Result (Array U64 120#usize) := do
  let rkeys := Array.repeat 120#usize 0#u64
  let (s, back) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice
    (core.slice.index.SliceIndexRangeToUsizeSlice U64)) rkeys ⟨8#usize⟩
  let first ← core.array.Array.index (core.ops.index.IndexSlice
    (core.slice.index.SliceIndexRangeToUsizeSlice U8)) key ⟨16#usize⟩
  let packed ← soft.fixslice.bitslice s first first first first
  let rkeys1 := back packed
  let (s1, back1) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice
    (core.slice.index.SliceIndexRangeUsizeSlice U64)) rkeys1 ⟨8#usize,16#usize⟩
  let second ← core.array.Array.index (core.ops.index.IndexSlice
    (core.slice.index.SliceIndexRangeFromUsizeSlice U8)) key ⟨16#usize⟩
  let packed1 ← soft.fixslice.bitslice s1 second second second second
  .ok (back1 packed1)

theorem initialState_spec (key : Nat → U8) :
    initialState (keyArray key) ⦃ result => result.val.map UScalar.bv =
      (network (fun _ index => (key index).bv)).list ++
        (network (fun _ index => (key (16 + index)).bv)).list ++ List.replicate 104 0#64 ⦄ := by
  unfold initialState
  simp only [key_first, key_second, bind_tc_ok]
  step*
  rw [s1_post3, s_post3, packed_post, packed1_post]
  simp [List.setSlice!, Array.repeat, wordSlice, Words.list]

theorem initialWords_network (key : Nat → BitVec 8) (offset : Nat) :
    TlsMpc.Signal.AesKeySchedule.initialWords key offset =
      (network (fun _ index => key (offset + index))).list := by
  have he (plane : Fin 8) :
      TlsMpc.Signal.AesKeySchedule.packWord
        (fun byte => byteValue (fun _ index => key (offset + index)) plane.val byte) =
      (network (fun _ index => key (offset + index))).at plane.val := by
    unfold TlsMpc.Signal.AesKeySchedule.packWord
    simp only [byteValue_network _ plane ⟨7,by decide⟩,
      byteValue_network _ plane ⟨6,by decide⟩, byteValue_network _ plane ⟨5,by decide⟩,
      byteValue_network _ plane ⟨4,by decide⟩, byteValue_network _ plane ⟨3,by decide⟩,
      byteValue_network _ plane ⟨2,by decide⟩, byteValue_network _ plane ⟨1,by decide⟩,
      byteValue_network _ plane ⟨0,by decide⟩]
    exact TlsMpc.Signal.AesKeySchedule.packWord_extract _
  unfold TlsMpc.Signal.AesKeySchedule.initialWords
  have hmap : (List.range 8).map (fun plane =>
      TlsMpc.Signal.AesKeySchedule.packWord
        (fun byte => byteValue (fun _ index => key (offset + index)) plane byte)) =
      (List.range 8).map (fun plane => (network (fun _ index => key (offset + index))).at plane) := by
    apply List.map_congr_left
    intro plane hp
    exact he ⟨plane,List.mem_range.mp hp⟩
  rw [hmap]
  rfl

end LibSignalReference.Candidate.AesKeySchedule
