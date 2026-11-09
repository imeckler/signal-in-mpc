import AesCtrBlockWork.ZipModelV1.StdBorrowZip
namespace LibSignalReference.Candidate.IndexedZipStd
open Aeneas Aeneas.Std
abbrev Zip64 := RustCryptoAesZipDiagnostic.Zip64
abbrev MutIter := RustCryptoAesZipDiagnostic.MutIter
abbrev SharedIter := RustCryptoAesZipDiagnostic.SharedIter
abbrev next := RustCryptoAesZipDiagnostic.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
 (⟨core.slice.iter.IteratorIterMut.next⟩)
 (core.iter.traits.iterator.IteratorSliceIter U64)

def ownerBack (position : Nat) (owner : Zip64) (returned : Option (U64×U64)) : Zip64 :=
 match returned with
 | none => owner
 | some (updated,_) =>
   {owner with fst:={owner.fst with slice:=owner.fst.slice.setAtNat position updated}}

theorem back_none (position : Nat) (owner : Zip64) : ownerBack position owner none=owner := rfl

theorem back_shared (position : Nat) (owner : Zip64) (returned : Option (U64×U64)) :
 (ownerBack position owner returned).snd=owner.snd := by
 cases returned with
 | none => rfl
 | some p => cases p; rfl

theorem back_cursors (position : Nat) (owner : Zip64) (returned : Option (U64×U64)) :
 (ownerBack position owner returned).fst.i=owner.fst.i ∧
 (ownerBack position owner returned).index=owner.index ∧
 (ownerBack position owner returned).len=owner.len := by
 cases returned with
 | none => exact ⟨rfl,rfl,rfl⟩
 | some p => cases p; exact ⟨rfl,rfl,rfl⟩

theorem back_length (position : Nat) (owner : Zip64) (returned : Option (U64×U64)) :
 (ownerBack position owner returned).fst.slice.length=owner.fst.slice.length := by
 cases returned with
 | none => rfl
 | some p => cases p; simp [ownerBack,Slice.setAtNat_length]

theorem back_updated (position : Nat) (owner : Zip64) (a b : U64)
 (bound : position<owner.fst.slice.length) :
 (ownerBack position owner (some (a,b))).fst.slice.val[position]?=some a := by
 simp [ownerBack,Slice.setAtNat,List.getElem?_set_self (by simpa [Slice.length]using bound)]

theorem back_untouched (position other : Nat) (owner : Zip64) (a b : U64) (different : position≠other) :
 (ownerBack position owner (some (a,b))).fst.slice.val[other]?=owner.fst.slice.val[other]? := by
 simp [ownerBack,Slice.setAtNat,List.getElem?_set_ne different]

theorem next_exhausted (owner : Zip64) (bound : owner.len≤owner.index) :
 next owner = .ok (none,owner,fun restored _=>restored) := by
 simp [next,RustCryptoAesZipDiagnostic.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,show ¬ owner.index<owner.len by omega]

theorem next_valid (left : MutIter) (right : SharedIter) (index : Nat)
 (bound : index<min (left.slice.length-left.i) (right.slice.length-right.i)) :
 ∃ a b,
 next {RustCryptoAesZipDiagnostic.fromIterators left right with index:=index} =
 .ok (some (a,b),{RustCryptoAesZipDiagnostic.fromIterators left right with index:=index+1},
   ownerBack (left.i+index)) := by
 have ha : left.i+index<left.slice.val.length := by
  have := Nat.lt_of_lt_of_le bound (Nat.min_le_left _ _)
  simp only [Slice.length]at this
  omega
 have hb : right.i+index<right.slice.val.length := by
  have := Nat.lt_of_lt_of_le bound (Nat.min_le_right _ _)
  simp only [Slice.length]at this
  omega
 refine ⟨left.slice.val[left.i+index],right.slice.val[right.i+index],?_⟩
 simp [next,RustCryptoAesZipDiagnostic.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
  RustCryptoAesZipDiagnostic.fromIterators,bound,List.getElem?_eq_getElem ha,List.getElem?_eq_getElem hb,ownerBack]
 rfl
end LibSignalReference.Candidate.IndexedZipStd
