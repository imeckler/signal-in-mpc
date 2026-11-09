import AesCtrBlockWork.ZipModelV1.ActualRoundKey
namespace LibSignalReference.Candidate.AesRoundKeyStdZip
open Aeneas Aeneas.Std
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

def array8 (value : Nat→U64) : Array U64 (8#usize) :=
 ⟨[value 0,value 1,value 2,value 3,value 4,value 5,value 6,value 7],by simp⟩
def slice8 (value : Nat→U64) : Slice U64 :=
 ⟨[value 0,value 1,value 2,value 3,value 4,value 5,value 6,value 7],by simp;scalar_tac⟩

abbrev Zip64 := RustCryptoAesZipDiagnostic.Zip64

def initialZip (state key : Nat→U64) : Zip64 :=
 RustCryptoAesZipDiagnostic.fromIterators
   ⟨(array8 state).to_slice,0⟩ ⟨slice8 key,0⟩
def atIndex (state key : Nat→U64) (index : Nat) : Zip64 :=
 {initialZip state key with index:=index}
def restore (z : Zip64) (index : Nat) (value : U64) : Zip64 :=
 {z with fst:={z.fst with slice:=z.fst.slice.setAtNat index value}}

theorem body_step (state key : Nat→U64) (index : Nat) (bound : index<8) (back : Zip64→Zip64) :
 RustCryptoAesZipDiagnostic.soft.fixslice.add_round_key_loop.body (atIndex state key index) back =
 .ok (.cont (atIndex state key (index+1),fun z=>back (restore z index (state index ^^^ key index)))) := by
 have cases : index=0 ∨ index=1 ∨ index=2 ∨ index=3 ∨ index=4 ∨ index=5 ∨ index=6 ∨ index=7 := by omega
 rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
  simp [RustCryptoAesZipDiagnostic.soft.fixslice.add_round_key_loop.body,
   RustCryptoAesZipDiagnostic.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
   RustCryptoAesZipDiagnostic.U64.Insts.CoreOpsBitBitXorAssignShared0U64.bitxor_assign,
   RustCryptoAesZipDiagnostic.U64.Insts.CoreOpsBitBitXorAssignU64.bitxor_assign,
   atIndex,initialZip,restore,RustCryptoAesZipDiagnostic.fromIterators,
   array8,slice8,Array.to_slice,Slice.length,lift]

theorem body_done (state key : Nat→U64) (back : Zip64→Zip64) :
 RustCryptoAesZipDiagnostic.soft.fixslice.add_round_key_loop.body (atIndex state key 8) back =
 .ok (.done (back (atIndex state key 8))) := by
 simp [RustCryptoAesZipDiagnostic.soft.fixslice.add_round_key_loop.body,
   RustCryptoAesZipDiagnostic.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
   atIndex,initialZip,RustCryptoAesZipDiagnostic.fromIterators,
   array8,slice8,Array.to_slice,Slice.length]
theorem setup (state key : Nat→U64) :
 RustCryptoAesZipDiagnostic.soft.fixslice.add_round_key (array8 state) (slice8 key) =
 (do
  let owner ← RustCryptoAesZipDiagnostic.soft.fixslice.add_round_key_loop (atIndex state key 0) id
  .ok (Array.from_slice (array8 state) owner.fst.slice)) := by
 with_unfolding_all rfl

/-- Actual source assertion/XOR/loop; trusted indexed Std borrow model only. -/
theorem actual_add_round_key (state key : Nat→U64) :
 RustCryptoAesZipDiagnostic.soft.fixslice.add_round_key (array8 state) (slice8 key) =
 .ok (array8 (fun i=>state i ^^^ key i)) := by
 with_unfolding_all rw [setup, RustCryptoAesZipDiagnostic.soft.fixslice.add_round_key_loop]
 with_unfolding_all rw [loop.eq_1]
 with_unfolding_all dsimp only
 with_unfolding_all rw [body_step state key 0 (by decide)]
 with_unfolding_all dsimp only
 with_unfolding_all rw [loop.eq_1]
 with_unfolding_all dsimp only
 with_unfolding_all rw [body_step state key 1 (by decide)]
 with_unfolding_all dsimp only
 with_unfolding_all rw [loop.eq_1]
 with_unfolding_all dsimp only
 with_unfolding_all rw [body_step state key 2 (by decide)]
 with_unfolding_all dsimp only
 with_unfolding_all rw [loop.eq_1]
 with_unfolding_all dsimp only
 with_unfolding_all rw [body_step state key 3 (by decide)]
 with_unfolding_all dsimp only
 with_unfolding_all rw [loop.eq_1]
 with_unfolding_all dsimp only
 with_unfolding_all rw [body_step state key 4 (by decide)]
 with_unfolding_all dsimp only
 with_unfolding_all rw [loop.eq_1]
 with_unfolding_all dsimp only
 with_unfolding_all rw [body_step state key 5 (by decide)]
 with_unfolding_all dsimp only
 with_unfolding_all rw [loop.eq_1]
 with_unfolding_all dsimp only
 with_unfolding_all rw [body_step state key 6 (by decide)]
 with_unfolding_all dsimp only
 with_unfolding_all rw [loop.eq_1]
 with_unfolding_all dsimp only
 with_unfolding_all rw [body_step state key 7 (by decide)]
 with_unfolding_all dsimp only
 with_unfolding_all rw [loop.eq_1]
 with_unfolding_all dsimp only
 with_unfolding_all rw [body_done]
 simp [restore,atIndex,initialZip,RustCryptoAesZipDiagnostic.fromIterators,
   array8,slice8,Array.to_slice,Array.from_slice,Slice.setAtNat,Slice.length]

theorem rejects_bad_key_length (state : Array U64 (8#usize)) (key : Slice U64) (bad : key.length≠8) :
 RustCryptoAesZipDiagnostic.soft.fixslice.add_round_key state key = .fail .assertionFailure := by
 have h : key.len≠8#usize := by scalar_tac
 simp [RustCryptoAesZipDiagnostic.soft.fixslice.add_round_key,h,massert]
theorem numeric_words (state key : Nat→U64) :
 ∃ output, RustCryptoAesZipDiagnostic.soft.fixslice.add_round_key (array8 state) (slice8 key) = .ok output ∧
 output.val.map UScalar.bv = (List.range 8).map (fun i=>(state i).bv ^^^ (key i).bv) := by
 refine ⟨array8 (fun i=>state i ^^^ key i),actual_add_round_key state key,?_⟩
 simp [array8,List.range_succ]
end LibSignalReference.Candidate.AesRoundKeyStdZip
