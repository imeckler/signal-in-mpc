import AesCtrBlockWork.EncryptBoundV1.SourceBindings
import LibSignalReference.Proofs.AesLayoutReference
import Mathlib.Tactic.FinCases
namespace LibSignalReference.Candidate.AesKeyRanges
open Aeneas Aeneas.Std TlsMpc.Signal.AesLayout
open LibSignalReference.Proofs.AesLayout
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def keyArray (keys : Nat→Words (BitVec 64)) : Array U64 (120#usize) :=
 ⟨(List.range 15).flatMap (fun r=>(keys r).list.map (fun value=>(⟨value⟩ : U64))),by simp [List.range_succ,Words.list]⟩
def start (r : Fin 15) : Usize :=
 match r.val with
 | 0=>0#usize | 1=>8#usize | 2=>16#usize | 3=>24#usize | 4=>32#usize
 | 5=>40#usize | 6=>48#usize | 7=>56#usize | 8=>64#usize | 9=>72#usize
 | 10=>80#usize | 11=>88#usize | 12=>96#usize | 13=>104#usize | _=>112#usize
def stop (r : Fin 15) : Usize :=
 match r.val with
 | 0=>8#usize | 1=>16#usize | 2=>24#usize | 3=>32#usize | 4=>40#usize
 | 5=>48#usize | 6=>56#usize | 7=>64#usize | 8=>72#usize | 9=>80#usize
 | 10=>88#usize | 11=>96#usize | 12=>104#usize | 13=>112#usize | _=>120#usize

theorem key_range (keys : Nat→Words (BitVec 64)) (r : Fin 15) :
 core.slice.index.SliceIndexRangeUsizeSlice.index {start:=start r,«end»:=stop r}
   (keyArray keys).to_slice = .ok (wordSlice (keys r.val)) := by
 fin_cases r <;> simp [core.slice.index.SliceIndexRangeUsizeSlice.index,start,stop,
   keyArray,Array.to_slice,Slice.length,wordSlice,Words.list,List.range_succ,List.slice]

theorem add8 (r : Fin 15) : ((start r + 8#usize) : Result Usize) = .ok (stop r) := by
 have spec:=UScalar.add_equiv (start r) (8#usize)
 generalize hcall : ((start r + 8#usize) : Result Usize)=out at spec
 cases out with
 | ok z=>
   have hz : z=stop r := by
    apply UScalar.eq_of_val_eq
    have hv:=spec.2.1
    fin_cases r <;> simp only [start,stop] at * <;> scalar_tac
   simpa only [hz] using hcall
 | fail error=>
   exfalso
   apply spec
   fin_cases r <;> simp only [start,stop] at * <;> scalar_tac
 | div=>exact False.elim spec

abbrev sourceRange := RustCryptoAesCtrBlock.ArrayU64120.Insts.CoreOpsIndexIndexspecialized_Type_a6d41e09652f1286a20c9e5d6cdaa143f56a848c0ded3779accf5fbb4661efb9.index

theorem source_range (keys : Nat→Words (BitVec 64)) (r : Fin 15) :
 sourceRange (keyArray keys) {start:=start r,«end»:=stop r} = .ok (wordSlice (keys r.val)) := by
 exact key_range keys r
end LibSignalReference.Candidate.AesKeyRanges
