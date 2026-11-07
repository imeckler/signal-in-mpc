import LibSignalReference.Generated.Unpadding.Funs
import TlsMpc.ByteAuth

namespace LibSignalReference.Proofs.Unpad

open Aeneas Aeneas.Std
open RustCryptoUnpadding

theorem any_body (it : core.slice.iter.Iter U8) (pad : U8) :
    core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any_loop.body
      Pkcs7.unpad.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool it pad =
    if h : it.i < it.slice.length then
      if it.slice[it.i] != pad then
        .ok (.done (true, { slice := it.slice, i := it.i + 1 }))
      else .ok (.cont ({ slice := it.slice, i := it.i + 1 }, pad))
    else .ok (.done (false, it)) := by
  unfold core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any_loop.body
  unfold core.slice.iter.IteratorSliceIter.next
  simp only [Slice.len_val]
  split <;> simp [Pkcs7.unpad.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool.call_mut] <;> rfl

theorem any_loop_spec (it : core.slice.iter.Iter U8) (pad : U8) :
    core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any_loop
      Pkcs7.unpad.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool it pad
      ⦃ result => result.1 = (it.slice.val.drop it.i).any (fun byte => byte != pad) ⦄ := by
  generalize hcount : it.slice.length - it.i = count
  induction count using Nat.strong_induction_on generalizing it with
  | h count ih =>
    unfold core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any_loop
    rw [loop]
    dsimp only
    rw [any_body]
    by_cases hi : it.i < it.slice.length
    · have hd := List.drop_eq_getElem_cons (l := it.slice.val) hi
      have hpost : (it.slice.val.drop it.i).any (fun byte => byte != pad) =
          ((it.slice[it.i] != pad) || (it.slice.val.drop (it.i + 1)).any (fun byte => byte != pad)) := by
        rw [hd, List.any_cons]
        rfl
      rw [dif_pos hi, hpost]
      by_cases hx : (it.slice[it.i] != pad) = true
      · simp [hx]
      · have hf : (it.slice[it.i] != pad) = false := Bool.eq_false_iff.mpr hx
        simp only [hf, Bool.false_eq_true, ↓reduceIte, Bool.false_or]
        exact ih (it.slice.length - (it.i + 1)) (by omega)
          { slice := it.slice, i := it.i + 1 } rfl
    · simp [hi, List.drop_eq_nil_of_le (by omega : it.slice.length ≤ it.i)]

@[step] theorem any_spec (it : core.slice.iter.Iter U8) (pad : U8) :
    core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any
      Pkcs7.unpad.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool it pad
      ⦃ result => result.1 = (it.slice.val.drop it.i).any (fun byte => byte != pad) ⦄ := by
  exact any_loop_spec it pad

def forgetResult : core.result.Result (Slice U8) RustCryptoUnpadding.Error → Option (List U8)
  | .Ok bytes => some bytes.val
  | .Err _ => none

def expected16 (block : List U8) (strict : Bool) : Option (List U8) :=
  let pad := block.getD 15 0#u8
  let count := pad.val
  if count = 0 ∨ 16 < count then none
  else if strict && (block.slice (16 - count) 15).any (fun byte => byte != pad) then none
  else some (block.take (16 - count))

theorem unpad_spec16 (block : Slice U8) (hsize : block.length = 16) (strict : Bool) :
    Pkcs7.unpad block strict ⦃ result => forgetResult result = expected16 block.val strict ⦄ := by
  unfold Pkcs7.unpad core.slice.Slice.iter
  step*
  all_goals
    have hi1 : i1.val = 15 := by scalar_tac
    have hpad : block.val.getD 15 0#u8 = n := by
      have hlt : 15 < block.val.length := by change 15 < block.length; omega
      have hn : n = block.val[15] := by simpa only [hi1] using n_post
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some, ← hn]
    simp only [forgetResult, expected16, hpad]
  · rename_i hz
    simp [hz]
  · have hn : 16 < n.val := by scalar_tac
    simp [hn]
  · have hn0 : n.val ≠ 0 := by scalar_tac
    have hnle : n.val ≤ 16 := by scalar_tac
    have hs : s.val = 16 - n.val := by scalar_tac
    simp_all [hs]

  · have hn0 : n.val ≠ 0 := by scalar_tac
    have hnle : n.val ≤ 16 := by scalar_tac
    have hs : s.val = 16 - n.val := by scalar_tac
    simp_all [hs]

  · have hn0 : n.val ≠ 0 := by scalar_tac
    have hnle : n.val ≤ 16 := by scalar_tac
    have hs : s.val = 16 - n.val := by scalar_tac
    simp_all [hs]

theorem raw_unpad_spec16 (block : Slice U8) (hsize : block.length = 16) :
    Pkcs7.Insts.Block_paddingPadding.raw_unpad block
      ⦃ result => forgetResult result = expected16 block.val true ⦄ := by
  exact unpad_spec16 block hsize true

end LibSignalReference.Proofs.Unpad
