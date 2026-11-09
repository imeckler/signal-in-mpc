import Aeneas
/-! TRUSTED scoped Std content/borrow model, not an extracted Zip proof.
Only the actual U64 IterMut×Iter indexed TrustedRandomAccess specialization
is modeled. Underlying iterator positions stay fixed; Zip.index advances.
No canonical Aeneas model is changed and no AES/XOR computation is supplied. -/
namespace RustCryptoAesZipDiagnostic
open Aeneas Aeneas.Std
structure core.iter.traits.iterator.Iterator (Self Item : Type) where
 next : Self → Result (Option Item × Self × (Self → Option Item → Self))

def core.iter.traits.iterator.IteratorSliceIter (T : Type) :=
 Aeneas.Std.core.iter.traits.iterator.IteratorSliceIter T

structure core.iter.adapters.zip.Zip (A B : Type) where
 fst : A
 snd : B
 index : Nat
 len : Nat

abbrev MutIter := Aeneas.Std.core.slice.iter.IterMut U64
abbrev SharedIter := Aeneas.Std.core.slice.iter.Iter U64
abbrev Zip64 := core.iter.adapters.zip.Zip MutIter SharedIter

def fromIterators (left : MutIter) (right : SharedIter) : Zip64 :=
 ⟨left,right,0,min (left.slice.length-left.i) (right.slice.length-right.i)⟩

def core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
 (_left : core.iter.traits.iterator.Iterator MutIter U64)
 (_right : Aeneas.Std.core.iter.traits.iterator.Iterator SharedIter U64)
 (z : Zip64) : Result (Option (U64×U64) × Zip64 × (Zip64 → Option (U64×U64) → Zip64)) :=
 if z.index < z.len then
   let ai:=z.fst.i+z.index
   let bi:=z.snd.i+z.index
   match z.fst.slice.val[ai]?,z.snd.slice.val[bi]? with
   | some a,some b =>
     .ok (some (a,b),{z with index:=z.index+1},fun restored returned =>
       match returned with
       | none => restored
       | some (updated,_) =>
         {restored with fst:={restored.fst with slice:=restored.fst.slice.setAtNat ai updated}})
   | _,_ => .fail .panic -- malformed descriptor outside constructor invariant
 else .ok (none,z,fun restored _ => restored)

def core.iter.traits.iterator.Iterator.zip.trait_default
 (_left : core.iter.traits.iterator.Iterator MutIter U64)
 (right : Aeneas.Std.core.iter.traits.collect.IntoIterator (Slice U64) U64 SharedIter)
 (self : MutIter) (other : Slice U64) : Result (Zip64 × (Zip64 → MutIter)) := do
 let shared ← right.into_iter other
 .ok (fromIterators self shared,fun restored => restored.fst)
end RustCryptoAesZipDiagnostic
