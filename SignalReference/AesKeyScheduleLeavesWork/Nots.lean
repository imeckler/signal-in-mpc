import AesKeyScheduleLeavesWork.SubBytes
import TlsMpc.Signal.AesKeySchedule

namespace LibSignalReference.Proofs.AesKeyScheduleLeaves

open Aeneas Aeneas.Std TlsMpc.Signal.AesLayout
open LibSignalReference.Proofs.AesLayout

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def notsSlice (words : Words (BitVec 64)) : Slice U64 :=
  wordSlice ⟨words.w0 ^^^ BitVec.allOnes 64, words.w1 ^^^ BitVec.allOnes 64,
    words.w2, words.w3, words.w4, words.w5 ^^^ BitVec.allOnes 64,
    words.w6 ^^^ BitVec.allOnes 64, words.w7⟩

theorem nots_reference (words : Words (BitVec 64)) :
    RustCryptoAesKeySchedule.soft.fixslice.sub_bytes_nots (wordSlice words) =
      .ok (notsSlice words) := by
  simp [RustCryptoAesKeySchedule.soft.fixslice.sub_bytes_nots, massert,
    wordSlice, Words.list, Slice.index_usize, Slice.update, lift, notsSlice]
  rfl

theorem nots_slice (state : Slice U64) (hlen : state.length = 8) :
    ∃ result, RustCryptoAesKeySchedule.soft.fixslice.sub_bytes_nots state = .ok result ∧
      result.val.map UScalar.bv =
        TlsMpc.Signal.AesKeySchedule.restoreNots TlsMpc.Signal.AesKeySchedule.concrete 0
          (state.val.map UScalar.bv) := by
  obtain ⟨words, rfl⟩ := slice_as_wordSlice state hlen
  refine ⟨notsSlice words, nots_reference words, ?_⟩
  simp [notsSlice, wordSlice, Words.list, TlsMpc.Signal.AesKeySchedule.restoreNots,
    TlsMpc.Signal.AesKeySchedule.concrete]
  exact ⟨BitVec.xor_allOnes, BitVec.xor_allOnes,
    BitVec.xor_allOnes, BitVec.xor_allOnes⟩

theorem nots_preserves_shape (state : Slice U64) (hlen : state.length = 8) :
    ∃ result, RustCryptoAesKeySchedule.soft.fixslice.sub_bytes_nots state = .ok result ∧
      result.length = 8 := by
  obtain ⟨words, rfl⟩ := slice_as_wordSlice state hlen
  refine ⟨notsSlice words, nots_reference words, ?_⟩
  simp [notsSlice, wordSlice, Words.list]

theorem nots_success_requires_shape (state result : Slice U64)
    (hresult : RustCryptoAesKeySchedule.soft.fixslice.sub_bytes_nots state = .ok result) :
    state.length = 8 := by
  by_contra hbad
  have hlen : Slice.len state ≠ 8#usize := by scalar_tac
  simp [RustCryptoAesKeySchedule.soft.fixslice.sub_bytes_nots, hlen, massert] at hresult

/-- The restored operation succeeds; its second actual Rust operation checks
the intermediate slice shape. This yields the raw operation's shape fact
without re-proving its Boolean network. -/
theorem sub_bytes_preserves_shape (state : Slice U64) (hlen : state.length = 8) :
    ∃ result, RustCryptoAesKeySchedule.soft.fixslice.sub_bytes state = .ok result ∧
      result.length = 8 := by
  obtain ⟨final, hfinal, _⟩ := restored_slice state hlen
  unfold restoredSubBytes at hfinal
  cases hraw : RustCryptoAesKeySchedule.soft.fixslice.sub_bytes state with
  | ok result =>
      simp only [hraw, bind_tc_ok] at hfinal
      exact ⟨result, rfl, nots_success_requires_shape result final hfinal⟩
  | fail error => simp [hraw] at hfinal
  | div => simp [hraw] at hfinal

end LibSignalReference.Proofs.AesKeyScheduleLeaves
