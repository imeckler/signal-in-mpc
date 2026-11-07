import AesKeyScheduleLeavesWork.Equalities
import LibSignalReference.Proofs.AesSubBytes
import LibSignalReference.Proofs.AesLayoutReference
import TlsMpc.Signal.AesKeyScheduleOps

namespace LibSignalReference.Proofs.AesKeyScheduleLeaves

open Aeneas Aeneas.Std TlsMpc.AesSbox TlsMpc.Signal.AesLayout
open LibSignalReference.Proofs.AesLayout

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def wordSboxOps : Ops (BitVec 64) := ⟨0, (· ^^^ ·), (· &&& ·), (~~~ ·)⟩

private theorem list_eight (xs : List α) (hlen : xs.length = 8) :
    ∃ a b c d e f g h, xs = [a,b,c,d,e,f,g,h] := by
  rcases List.exists_of_length_succ (n := 7) xs hlen with ⟨a, xs, rfl⟩
  simp at hlen
  rcases List.exists_of_length_succ (n := 6) xs hlen with ⟨b, xs, rfl⟩
  simp at hlen
  rcases List.exists_of_length_succ (n := 5) xs hlen with ⟨c, xs, rfl⟩
  simp at hlen
  rcases List.exists_of_length_succ (n := 4) xs hlen with ⟨d, xs, rfl⟩
  simp at hlen
  rcases List.exists_of_length_succ (n := 3) xs hlen with ⟨e, xs, rfl⟩
  simp at hlen
  rcases List.exists_of_length_succ (n := 2) xs hlen with ⟨f, xs, rfl⟩
  simp at hlen
  rcases List.exists_of_length_succ (n := 1) xs hlen with ⟨g, xs, rfl⟩
  simp at hlen
  rcases List.exists_of_length_succ (n := 0) xs hlen with ⟨h, xs, rfl⟩
  simp at hlen
  subst xs
  exact ⟨a,b,c,d,e,f,g,h,rfl⟩

theorem slice_as_wordSlice (state : Slice U64) (hlen : state.length = 8) :
    ∃ words : Words (BitVec 64), state = wordSlice words := by
  rcases list_eight state.val hlen with ⟨a,b,c,d,e,f,g,h,hvalues⟩
  refine ⟨⟨a.bv,b.bv,c.bv,d.bv,e.bv,f.bv,g.bv,h.bv⟩, ?_⟩
  apply Subtype.ext
  simpa [wordSlice, Words.list] using hvalues

theorem unpack_pack (xs : List (BitVec 1)) (hlen : xs.length = 8) :
    (List.range 8).map (fun bit => (packValue xs).extractLsb' bit 1) = xs := by
  rcases list_eight xs hlen with ⟨a,b,c,d,e,f,g,h,rfl⟩
  exact AesSubBytes.bits_of_packed a b c d e f g h

theorem pack_injective (xs ys : List (BitVec 1))
    (hx : xs.length = 8) (hy : ys.length = 8) (h : packValue xs = packValue ys) : xs = ys := by
  rw [← unpack_pack xs hx, h, unpack_pack ys hy]

theorem bit_network_eq_circuit (xs : List (BitVec 1)) (hlen : xs.length = 8) :
    AesNetwork.run concrete xs = circuit concrete xs := by
  apply pack_injective
  · simp [AesNetwork.run, AesNetwork.indices]
  · simp [circuit, outputIndices]
  rcases list_eight xs hlen with ⟨a,b,c,d,e,f,g,h,rfl⟩
  rw [AesSubBytes.network_byte]
  simp only [TlsMpc.AesSbox.value, AesSubBytes.bits_of_packed]

def wordLane (n : Nat) (x : BitVec 64) : BitVec 1 := x.extractLsb' n 1

theorem wordLaneHom (n : Nat) (hn : n < 64) : Hom wordSboxOps concrete (wordLane n) := by
  constructor
  · simp [wordLane, wordSboxOps, concrete]
  · intros; simp [wordLane, wordSboxOps, concrete, BitVec.extractLsb'_xor]
  · intros; simp [wordLane, wordSboxOps, concrete, BitVec.extractLsb'_and]
  · intro x
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have he : i = 0 := by omega
    subst i
    simp [wordLane, wordSboxOps, concrete, hn]

/-- The already-proved per-byte implementation comparison lifts to all eight
arbitrary 64-bit words. No restriction is imposed on any parallel lane. -/
theorem word_network_eq_circuit (xs : List (BitVec 64)) (hlen : xs.length = 8) :
    AesNetwork.run wordSboxOps xs = circuit wordSboxOps xs := by
  apply List.ext_getElem
  · simp [AesNetwork.run, AesNetwork.indices, circuit, outputIndices]
  intro index hi hj
  apply BitVec.eq_of_getLsbD_eq
  intro lane hlane
  have hlanes : (AesNetwork.run wordSboxOps xs).map (wordLane lane) =
      (circuit wordSboxOps xs).map (wordLane lane) := by
    rw [AesNetwork.run_map (wordLaneHom lane hlane), circuit_map (wordLaneHom lane hlane)]
    exact bit_network_eq_circuit _ (by simp [hlen])
  have hentry := congrArg (fun values : List (BitVec 1) => (values[index]?.getD 0).getLsbD 0) hlanes
  simpa [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, wordLane] using hentry

def restoredSubBytes (state : Slice U64) : Result (Slice U64) := do
  let state ← RustCryptoAesKeySchedule.soft.fixslice.sub_bytes state
  RustCryptoAesKeySchedule.soft.fixslice.sub_bytes_nots state

theorem restoredSubBytes_eq : restoredSubBytes = AesSubBytes.translated := by
  funext state
  simp only [restoredSubBytes, AesSubBytes.translated, sub_bytes_eq, sub_bytes_nots_eq]

theorem restored_word_list (a b c d e f g h : U64) :
    ∃ result, restoredSubBytes (AesSubBytes.input a b c d e f g h) = .ok result ∧
      result.val.map UScalar.bv = circuit wordSboxOps [a.bv,b.bv,c.bv,d.bv,e.bv,f.bv,g.bv,h.bv] := by
  refine ⟨AesSubBytes.output a b c d e f g h, ?_, ?_⟩
  · rw [restoredSubBytes_eq]
    exact AesSubBytes.translated_network a b c d e f g h
  · change (AesNetwork.run AesSubBytes.wordOps [a,b,c,d,e,f,g,h]).map UScalar.bv = _
    rw [AesNetwork.run_map AesSubBytes.wordHom]
    exact word_network_eq_circuit _ (by simp)

def sboxSlice (words : Words (BitVec 64)) : Slice U64 :=
  ⟨(circuit wordSboxOps words.list).map (fun word => ⟨word⟩), by
    simp [circuit, outputIndices]; scalar_tac⟩

theorem restored_wordSlice (words : Words (BitVec 64)) :
    restoredSubBytes (wordSlice words) = .ok (sboxSlice words) := by
  obtain ⟨result, hr, hv⟩ := restored_word_list
    ⟨words.w0⟩ ⟨words.w1⟩ ⟨words.w2⟩ ⟨words.w3⟩
    ⟨words.w4⟩ ⟨words.w5⟩ ⟨words.w6⟩ ⟨words.w7⟩
  change restoredSubBytes (wordSlice words) = .ok result at hr
  rw [hr]
  congr 1
  apply Subtype.ext
  have hback := congrArg (fun values : List (BitVec 64) => values.map (fun word => (⟨word⟩ : U64))) hv
  simpa [List.map_map, Function.comp_def, sboxSlice, Words.list] using hback

/-- Slice-form bridge for composing actual array-window borrows. -/
theorem restored_slice (state : Slice U64) (hlen : state.length = 8) :
    ∃ result, restoredSubBytes state = .ok result ∧
      result.val.map UScalar.bv =
        circuit TlsMpc.Signal.AesKeySchedule.wordOps (state.val.map UScalar.bv) := by
  obtain ⟨words, rfl⟩ := slice_as_wordSlice state hlen
  refine ⟨sboxSlice words, restored_wordSlice words, ?_⟩
  simp [sboxSlice, wordSlice, List.map_map, Function.comp_def, Words.list,
    wordSboxOps, TlsMpc.Signal.AesKeySchedule.wordOps]

theorem restored_rejects_shape (state : Slice U64) (hlen : state.length ≠ 8) :
    restoredSubBytes state = .fail .assertionFailure := by
  rw [restoredSubBytes_eq]
  exact AesSubBytes.translated_bad_length state hlen

end LibSignalReference.Proofs.AesKeyScheduleLeaves
