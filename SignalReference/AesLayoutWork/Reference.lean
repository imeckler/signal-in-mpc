import AesLayoutWork.Generated.Bitslice.Funs
import AesLayoutWork.Network

namespace SignalReference.AesLayout

open Aeneas Aeneas.Std TlsMpc.Signal.AesLayout

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def slice12 (input : Nat → U8) : Slice U8 :=
  ⟨[input 0,input 1,input 2,input 3,input 4,input 5,input 6,input 7,
    input 8,input 9,input 10,input 11], by simp; scalar_tac⟩

def slice16 (input : Nat → U8) : Slice U8 :=
  ⟨[input 0,input 1,input 2,input 3,input 4,input 5,input 6,input 7,
    input 8,input 9,input 10,input 11,input 12,input 13,input 14,input 15], by simp; scalar_tac⟩

def wordSlice (words : Words (BitVec 64)) : Slice U64 :=
  ⟨words.list.map (fun word => ⟨word⟩), by simp [Words.list]; scalar_tac⟩

theorem shift_left_u32 (x : U64) (s : U32) (hs : s.val < 64) :
    (x <<< s) = .ok ⟨x.bv <<< s.val⟩ := by
  change (if s.val < 64 then _ else _) = _
  simp only [hs, if_pos]
  rfl

theorem shift_right_u32 (x : U64) (s : U32) (hs : s.val < 64) :
    (x >>> s) = .ok ⟨x.bv >>> s.val⟩ := by
  change (if s.val < 64 then _ else _) = _
  simp only [hs, if_pos]
  rfl

theorem shift_left_i32 (x : U64) (s : I32) (hs0 : 0 ≤ s.val) (hs : s.toNat < 64) :
    (x <<< s) = .ok ⟨x.bv <<< s.toNat⟩ := by
  change (if s.val ≥ 0 then (if s.toNat < 64 then _ else _) else _) = _
  simp only [hs0, hs, if_pos]
  rfl

theorem read_refines (input : Nat → U8) :
    RustCryptoAesLayout.soft.fixslice.bitslice.read_reordered (slice12 input) =
      .ok ⟨readReordered (fun i => (input i).bv)⟩ := by
  simp [RustCryptoAesLayout.soft.fixslice.bitslice.read_reordered, slice12,
    Slice.index_usize, readReordered, lift, shift_left_i32,
    core.convert.num.FromU64U8.from]
  rfl

theorem delta_refines (a b mask : U64) (shift : U32) (hshift : shift.val < 64) :
    RustCryptoAesLayout.soft.fixslice.delta_swap_2 a b shift mask =
      .ok (⟨(deltaSwap a.bv b.bv shift.val mask.bv).1⟩,
        ⟨(deltaSwap a.bv b.bv shift.val mask.bv).2⟩) := by
  simp [RustCryptoAesLayout.soft.fixslice.delta_swap_2, deltaSwap, lift,
    shift_right_u32 _ _ hshift, shift_left_u32 _ _ hshift]
  exact ⟨rfl, rfl⟩

theorem first_range (input : Nat → U8) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      (slice16 input) { start := 0#usize, «end» := 12#usize } =
      .ok (slice12 input) := by
  simp [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index, Slice.subslice,
    slice16, slice12, List.slice]

theorem second_range (input : Nat → U8) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      (slice16 input) { start := 4#usize, «end» := 16#usize } =
      .ok (slice12 (fun n => input (n + 4))) := by
  simp [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index, Slice.subslice,
    slice16, slice12, List.slice]

theorem bitslice_network (input : Nat → Nat → U8) (initial : Words (BitVec 64)) :
    RustCryptoAesLayout.soft.fixslice.bitslice (wordSlice initial)
      (slice16 (input 0)) (slice16 (input 1)) (slice16 (input 2)) (slice16 (input 3)) =
      .ok (wordSlice (network (fun b i => (input b i).bv))) := by
  have hlen (hx : 8 < 2 ^ UScalarTy.Usize.numBits) : Usize.ofNatCore 8 hx = 8#usize := by scalar_tac
  have hlen16 (hx : 16 < 2 ^ UScalarTy.Usize.numBits) : Usize.ofNatCore 16 hx = 16#usize := by scalar_tac
  simp only [RustCryptoAesLayout.soft.fixslice.bitslice, first_range, second_range,
    read_refines]
  simp [Slice.len, wordSlice, Words.list, slice16, massert, hlen, hlen16,
    first_range, second_range, read_refines, delta_refines, Slice.update,
    network, transpose, prepare]

end SignalReference.AesLayout
