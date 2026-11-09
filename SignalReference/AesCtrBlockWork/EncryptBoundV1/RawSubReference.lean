import AesCtrBlockWork.EncryptBoundV1.SourceBindings
import LibSignalReference.Proofs.AesNetwork
import LibSignalReference.Proofs.AesLayoutReference
import Mathlib.Tactic.IntervalCases
namespace LibSignalReference.Candidate.AesRawSub
open Aeneas Aeneas.Std TlsMpc.AesSbox
open LibSignalReference.Proofs
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def wordOps : Ops U64 := ⟨0#u64,(· ^^^ ·),(· &&& ·),(· ^^^ 18446744073709551615#u64)⟩
def vectorOps : Ops (BitVec 64) := ⟨0,(· ^^^ ·),(· &&& ·),(~~~ ·)⟩
def rawRun (o : Ops B) (input : List B) : List B :=
 let values:=TlsMpc.AesSbox.run o AesNetwork.rawProgram input
 AesNetwork.rawIndices.map (fun i=>values[i]?.getD o.zero)
def input (a b c d e f g h : U64) : Slice U64 :=
 ⟨[a,b,c,d,e,f,g,h],by simp;scalar_tac⟩
def output (a b c d e f g h : U64) : Slice U64 :=
 ⟨rawRun wordOps [a,b,c,d,e,f,g,h],by simp [rawRun,AesNetwork.rawIndices];scalar_tac⟩

theorem actual_raw (a b c d e f g h : U64) :
 RustCryptoAesCtrBlock.soft.fixslice.sub_bytes (input a b c d e f g h) =
 .ok (output a b c d e f g h) := by
 have hlen (hx : 8 < 2 ^ UScalarTy.Usize.numBits) : Usize.ofNatCore 8 hx = 8#usize := by scalar_tac
 simp [RustCryptoAesCtrBlock.soft.fixslice.sub_bytes,
  RustCryptoAesSubBytes.soft.fixslice.sub_bytes,input,output,rawRun,
  Slice.len,Slice.index_usize,Slice.update,lift,hlen,massert,
  AesNetwork.rawProgram,AesNetwork.rawIndices,TlsMpc.AesSbox.run,gate,wordOps]

theorem wordHom : Hom wordOps vectorOps (fun x : U64=>x.bv) := by
 constructor
 · rfl
 · intros; rfl
 · intros; rfl
 · intro x
   change x.bv ^^^ (BitVec.allOnes 64) = ~~~x.bv
   exact BitVec.xor_allOnes

theorem rawRun_map {B B' : Type} {a : Ops B} {b : Ops B'} {f : B→B'}
 (h : Hom a b f) (xs : List B) : (rawRun a xs).map f=rawRun b (xs.map f) := by
 simp only [rawRun, ← TlsMpc.AesSbox.run_map h, List.map_map, Function.comp_def,
   ← h.zero,TlsMpc.AesSbox.get_map]

theorem output_value (a b c d e f g h : U64) :
 (output a b c d e f g h).val.map UScalar.bv =
 rawRun vectorOps [a.bv,b.bv,c.bv,d.bv,e.bv,f.bv,g.bv,h.bv] := by
 exact rawRun_map wordHom _

open TlsMpc.Signal.AesLayout LibSignalReference.Proofs.AesLayout

def wordsFromList (xs : List (BitVec 64)) : Words (BitVec 64) :=
 ⟨xs[0]?.getD 0,xs[1]?.getD 0,xs[2]?.getD 0,xs[3]?.getD 0,
  xs[4]?.getD 0,xs[5]?.getD 0,xs[6]?.getD 0,xs[7]?.getD 0⟩

theorem wordsFromList_list (xs : List (BitVec 64)) (hlen : xs.length=8) :
 (wordsFromList xs).list=xs := by
 apply List.ext_getElem
 · simp [Words.list,hlen]
 · intro i hi hx
   have hi8 : i<8 := by simpa [Words.list] using hi
   interval_cases i <;> simp [wordsFromList,Words.list,hx]

def rawWords (words : Words (BitVec 64)) : Words (BitVec 64) :=
 wordsFromList (rawRun vectorOps words.list)

theorem rawWords_list (words : Words (BitVec 64)) :
 (rawWords words).list=rawRun vectorOps words.list := by
 apply wordsFromList_list
 simp [rawRun,AesNetwork.rawIndices]

theorem output_words (words : Words (BitVec 64)) :
 output ⟨words.w0⟩ ⟨words.w1⟩ ⟨words.w2⟩ ⟨words.w3⟩
   ⟨words.w4⟩ ⟨words.w5⟩ ⟨words.w6⟩ ⟨words.w7⟩ = wordSlice (rawWords words) := by
 apply Subtype.ext
 have restore (xs : List U64) : (xs.map UScalar.bv).map (fun byte=>(⟨byte⟩ : U64))=xs := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>simp only [List.map_cons,ih]
 let out:=output (⟨words.w0⟩ : U64) ⟨words.w1⟩ ⟨words.w2⟩ ⟨words.w3⟩
   ⟨words.w4⟩ ⟨words.w5⟩ ⟨words.w6⟩ ⟨words.w7⟩
 change out.val=(wordSlice (rawWords words)).val
 calc
  out.val=(out.val.map UScalar.bv).map (fun byte=>(⟨byte⟩ : U64)) := (restore _).symm
  _=(rawRun vectorOps words.list).map (fun byte=>(⟨byte⟩ : U64)) := by
    exact congrArg (List.map (fun byte : BitVec 64=>(⟨byte⟩ : U64)))
      (output_value ⟨words.w0⟩ ⟨words.w1⟩ ⟨words.w2⟩ ⟨words.w3⟩
        ⟨words.w4⟩ ⟨words.w5⟩ ⟨words.w6⟩ ⟨words.w7⟩)
  _=_ := by rw [←rawWords_list];rfl

theorem actual_words (words : Words (BitVec 64)) :
 RustCryptoAesCtrBlock.soft.fixslice.sub_bytes (wordSlice words) =
 .ok (wordSlice (rawWords words)) := by
 have h:=actual_raw (⟨words.w0⟩ : U64) ⟨words.w1⟩ ⟨words.w2⟩ ⟨words.w3⟩
   ⟨words.w4⟩ ⟨words.w5⟩ ⟨words.w6⟩ ⟨words.w7⟩
 rw [output_words] at h
 exact h

theorem rejects_bad_length (state : Slice U64) (bad : state.length≠8) :
 RustCryptoAesCtrBlock.soft.fixslice.sub_bytes state = .fail .assertionFailure := by
 have hlen : state.len≠8#usize := by scalar_tac
 simp [RustCryptoAesCtrBlock.soft.fixslice.sub_bytes,
   RustCryptoAesSubBytes.soft.fixslice.sub_bytes,hlen,massert]
end LibSignalReference.Candidate.AesRawSub
