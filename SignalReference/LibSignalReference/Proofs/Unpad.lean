import LibSignalReference.Proofs.UnpadReference
import TlsMpc.Signal.Unpad

namespace LibSignalReference.Proofs.Unpad

open Aeneas Aeneas.Std

def padByte (count : Nat) : U8 := ⟨BitVec.ofNat 8 count⟩

def Matches (block : List U8) (count : Nat) : Prop :=
  block.drop (16 - count) = List.replicate count (padByte count)

instance (block : List U8) (count : Nat) : Decidable (Matches block count) :=
  inferInstanceAs (Decidable (_ = _))

theorem caseMask_reference (block : List U8) (count : Nat) :
    TlsMpc.Signal.Unpad.caseMask TlsMpc.ByteAuth.concrete
      (block.map (fun byte => byte.bv)) count =
      if Matches block count then 255 else 0 := by
  unfold TlsMpc.Signal.Unpad.caseMask
  rw [TlsMpc.ByteAuth.equalMask_value]
  have hm : (block.map (fun byte => byte.bv)).drop (16 - count) =
      List.replicate count (TlsMpc.ByteAuth.concrete.const count) ↔ Matches block count := by
    constructor
    · intro h
      apply (List.map_inj_right (fun (a b : U8) hab => U8.bv_eq_imp_eq a b hab)).mp
      simpa [Matches, padByte, TlsMpc.ByteAuth.concrete] using h
    · intro h
      have := congrArg (List.map (fun (byte : U8) => byte.bv)) h
      simpa [Matches, padByte, TlsMpc.ByteAuth.concrete] using this
  simp only [hm]

theorem matches_last (block : List U8) (hblock : block.length = 16) (count : Nat)
    (hpos : 0 < count) (hcount : count ≤ 16) (hm : Matches block count) :
    block.getD 15 0#u8 = padByte count := by
  have heq := congrArg (fun xs => xs.getD (count - 1) 0#u8) hm
  have hi : 16 - count + (count - 1) = 15 := by omega
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_replicate, hi,
    show count - 1 < count by omega] at heq
  simpa [List.getD_eq_getElem?_getD] using heq

theorem matches_count_value (block : List U8) (hblock : block.length = 16) (count : Nat)
    (hpos : 0 < count) (hcount : count ≤ 16) (hm : Matches block count) :
    (block.getD 15 0#u8).val = count := by
  rw [matches_last block hblock count hpos hcount hm]
  change count % 256 = count
  exact Nat.mod_eq_of_lt (by omega)

theorem suffix_split (block : List U8) (hblock : block.length = 16)
    (start : Nat) (hstart : start ≤ 15) :
    block.drop start = block.slice start 15 ++ [block.getD 15 0#u8] := by
  have h15 : 15 < block.length := by omega
  have hlast : block.drop 15 = [block.getD 15 0#u8] := by
    rw [List.drop_eq_getElem_cons h15]
    simp [List.drop_eq_nil_of_le (by omega : block.length ≤ 16),
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h15]
  have hsplit := List.take_append_drop (15 - start) (block.drop start)
  rw [List.drop_drop, show start + (15 - start) = 15 by omega, hlast] at hsplit
  simpa [List.slice] using hsplit.symm

theorem matches_iff (block : List U8) (hblock : block.length = 16) (count : Nat)
    (hpos : 0 < count) (hcount : count ≤ 16)
    (hlast : block.getD 15 0#u8 = padByte count) :
    Matches block count ↔
      (block.slice (16 - count) 15).any (fun byte => byte != block.getD 15 0#u8) = false := by
  unfold Matches
  have hlen : (block.drop (16 - count)).length = count := by simp [hblock]; omega
  rw [List.eq_replicate_iff]
  simp only [hlen, true_and]
  rw [suffix_split block hblock (16 - count) (by omega), List.any_eq_false]
  rw [hlast]
  simp only [List.mem_append, List.mem_singleton, or_imp, forall_and, forall_eq,
    bne_iff_ne, not_not, and_true]

theorem decodeCases_reject (block : List U8) (hblock : block.length = 16)
    (counts : List Nat) (hcounts : ∀ count ∈ counts, count ≤ 16)
    (hfailed : ∀ count ∈ counts, ¬Matches block count) :
    TlsMpc.Signal.Unpad.decodeCases TlsMpc.ByteAuth.concrete
      (block.map (fun byte => byte.bv)) counts = List.replicate 18 0 := by
  induction counts with
  | nil => rfl
  | cons count counts ih =>
    have hc : count ≤ 16 := hcounts count (by simp)
    have ht : ∀ c ∈ counts, c ≤ 16 := by intro c hm; exact hcounts c (by simp [hm])
    have hf : ¬Matches block count := hfailed count (by simp)
    have htail : ∀ c ∈ counts, ¬Matches block c := by intro c hm; exact hfailed c (by simp [hm])
    rw [TlsMpc.Signal.Unpad.decodeCases, caseMask_reference, if_neg hf,
      TlsMpc.Signal.Unpad.choose_reject]
    · exact ih ht htail
    · rw [TlsMpc.Signal.Unpad.retained_length _ _ (by simpa using hblock) count hc,
        TlsMpc.Signal.Unpad.decodeCases_length _ _ (by simpa using hblock) counts ht]

theorem decodeCases_accept (block : List U8) (hblock : block.length = 16)
    (counts : List Nat) (hcounts : ∀ count ∈ counts, count ≤ 16)
    (count : Nat) (hmem : count ∈ counts) (hm : Matches block count)
    (hunique : ∀ other ∈ counts, Matches block other → other = count) :
    TlsMpc.Signal.Unpad.decodeCases TlsMpc.ByteAuth.concrete
      (block.map (fun byte => byte.bv)) counts =
    TlsMpc.Signal.Unpad.retained TlsMpc.ByteAuth.concrete
      (block.map (fun byte => byte.bv)) count := by
  induction counts with
  | nil => simp at hmem
  | cons first rest ih =>
    have hc : first ≤ 16 := hcounts first (by simp)
    have ht : ∀ c ∈ rest, c ≤ 16 := by intro c hm; exact hcounts c (by simp [hm])
    have heq : (TlsMpc.Signal.Unpad.retained TlsMpc.ByteAuth.concrete
        (block.map (fun byte => byte.bv)) first).length =
        (TlsMpc.Signal.Unpad.decodeCases TlsMpc.ByteAuth.concrete
          (block.map (fun byte => byte.bv)) rest).length := by
      rw [TlsMpc.Signal.Unpad.retained_length _ _ (by simpa using hblock) first hc,
        TlsMpc.Signal.Unpad.decodeCases_length _ _ (by simpa using hblock) rest ht]
    rw [TlsMpc.Signal.Unpad.decodeCases, caseMask_reference]
    by_cases hf : Matches block first
    · rw [if_pos hf, TlsMpc.Signal.Unpad.choose_accept _ _ heq,
        hunique first (by simp) hf]
    · rw [if_neg hf, TlsMpc.Signal.Unpad.choose_reject _ _ heq]
      apply ih ht
      · simp only [List.mem_cons] at hmem
        rcases hmem with h | h
        · exact False.elim (hf (h ▸ hm))
        · exact h
      · intro c hc hm
        exact hunique c (by simp [hc]) hm

def encodeOption : Option (List U8) → List (BitVec 8)
  | none => List.replicate 18 0
  | some bytes => [255, BitVec.ofNat 8 bytes.length] ++ bytes.map (fun byte => byte.bv) ++
      List.replicate (16 - bytes.length) 0

theorem decode_reference (block : List U8) (hblock : block.length = 16) :
    TlsMpc.Signal.Unpad.decode TlsMpc.ByteAuth.concrete (block.map (fun byte => byte.bv)) =
      encodeOption (expected16 block true) := by
  let counts := (List.range 16).map (· + 1)
  have hb : ∀ k ∈ counts, 0 < k ∧ k ≤ 16 := by
    intro k hk
    rcases List.mem_map.mp hk with ⟨n, hn, hk⟩
    simp only [List.mem_range] at hn
    omega
  have hbound : ∀ k ∈ counts, k ≤ 16 := by intro k hk; exact (hb k hk).2
  generalize hcount : (block.getD 15 0#u8).val = count
  have hu : ∀ k ∈ counts, Matches block k → k = count := by
    intro k hk hm
    have := matches_count_value block hblock k (hb k hk).1 (hb k hk).2 hm
    omega
  change TlsMpc.Signal.Unpad.decodeCases TlsMpc.ByteAuth.concrete
    (block.map (fun byte => byte.bv)) counts = _
  by_cases hv : 0 < count ∧ count ≤ 16
  · have hmem : count ∈ counts := by
      apply List.mem_map.mpr
      exact ⟨count - 1, by simp; omega, by omega⟩
    have hlast : block.getD 15 0#u8 = padByte count := by
      apply UScalar.eq_of_val_eq
      change (block.getD 15 0#u8).val = count % 256
      rw [hcount, Nat.mod_eq_of_lt (by omega)]
    by_cases hm : Matches block count
    · have ha := (matches_iff block hblock count hv.1 hv.2 hlast).mp hm
      rw [decodeCases_accept block hblock counts hbound count hmem hm hu]
      simp only [expected16, hcount, show ¬(count = 0 ∨ 16 < count) by omega,
        ↓reduceIte, Bool.true_and, ha, Bool.false_eq_true]
      simp only [encodeOption, TlsMpc.Signal.Unpad.retained, TlsMpc.ByteAuth.concrete,
        List.length_take, hblock, Nat.min_eq_left (by omega : 16 - count ≤ 16),
        show 16 - (16 - count) = count by omega, List.map_take]
      rfl
    · have ha : (block.slice (16 - count) 15).any (fun byte => byte != block.getD 15 0#u8) = true := by
        have hn := (matches_iff block hblock count hv.1 hv.2 hlast).not.mp hm
        cases heq : (block.slice (16 - count) 15).any (fun byte => byte != block.getD 15 0#u8)
        · exact False.elim (hn heq)
        · rfl
      rw [decodeCases_reject block hblock counts hbound (by
        intro k hk hmatch
        exact hm ((hu k hk hmatch) ▸ hmatch))]
      simp only [expected16, hcount, show ¬(count = 0 ∨ 16 < count) by omega,
        ↓reduceIte, Bool.true_and, ha, encodeOption]
  · rw [decodeCases_reject block hblock counts hbound (by
      intro k hk hmatch
      have := hu k hk hmatch
      have := hb k hk
      omega)]
    have hbad : count = 0 ∨ 16 < count := by omega
    simp only [expected16, hcount, hbad, ↓reduceIte, encodeOption]

theorem unpad_refines_artifact (block : Slice U8) (hsize : block.length = 16)
    (secret : List (_root_.Std.Tactic.BVDecide.BVExpr 8))
    (assign : _root_.Std.Tactic.BVDecide.BVExpr.Assignment)
    (hsecret : secret.map (_root_.Std.Tactic.BVDecide.BVExpr.eval assign) =
      block.val.map (fun byte => byte.bv)) :
    ∃ result, RustCryptoUnpadding.Pkcs7.Insts.Block_paddingPadding.raw_unpad block = .ok result ∧
      ∀ (index : Nat)
        (hi : index < 8 * (TlsMpc.Signal.Unpad.decode TlsMpc.ByteAuth.symbolic secret).length),
        TlsMpc.AigExport.evalRef
          (TlsMpc.AigExport.exportNodes (TlsMpc.AigExport.compile
            (TlsMpc.ByteCircuit.joinExpr (TlsMpc.Signal.Unpad.decode TlsMpc.ByteAuth.symbolic secret))).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (TlsMpc.AigExport.exportRef ((TlsMpc.AigExport.compile
            (TlsMpc.ByteCircuit.joinExpr (TlsMpc.Signal.Unpad.decode TlsMpc.ByteAuth.symbolic secret))).vec.get index hi)) =
          (TlsMpc.ByteCircuit.joinValue (encodeOption (forgetResult result))).getLsbD index := by
  obtain ⟨result, hr, hv⟩ := WP.spec_imp_exists (raw_unpad_spec16 block hsize)
  refine ⟨result, hr, ?_⟩
  intro index hi
  rw [TlsMpc.Signal.Unpad.compiled_decode_correct, hsecret, decode_reference block.val hsize, hv]

/-- A mathematical decoder for the shared output representation. It is used
    only to show that accepted length and bytes are losslessly represented. -/
def recoverEncoding (encoded : List (BitVec 8)) : Option (List (BitVec 8)) :=
  if encoded.getD 0 0 = 255 then
    some ((encoded.drop 2).take (encoded.getD 1 0).toNat)
  else none

theorem recover_encodeOption (bytes : Option (List U8))
    (hsize : ∀ message ∈ bytes, message.length ≤ 16) :
    recoverEncoding (encodeOption bytes) = bytes.map (List.map (fun byte => byte.bv)) := by
  cases bytes with
  | none => rfl
  | some message =>
    have hlen : message.length ≤ 16 := hsize message (by simp)
    have hnat : (BitVec.ofNat 8 message.length).toNat = message.length := by
      exact Nat.mod_eq_of_lt (by omega)
    simp [recoverEncoding, encodeOption, hnat]

theorem encodeOption_injective (a b : Option (List U8))
    (ha : ∀ message ∈ a, message.length ≤ 16)
    (hb : ∀ message ∈ b, message.length ≤ 16)
    (heq : encodeOption a = encodeOption b) : a = b := by
  have h := congrArg recoverEncoding heq
  rw [recover_encodeOption a ha, recover_encodeOption b hb] at h
  cases a with
  | none => cases b with
    | none => rfl
    | some _ => cases h
  | some xs => cases b with
    | none => cases h
    | some ys =>
      apply congrArg some
      exact (List.map_inj_right (fun (x y : U8) hxy => U8.bv_eq_imp_eq x y hxy)).mp
        (Option.some.inj h)

theorem forgetResult_injective : Function.Injective forgetResult := by
  intro a b h
  cases a with
  | Ok xs => cases b with
    | Ok ys =>
      apply congrArg core.result.Result.Ok
      apply Subtype.ext
      exact Option.some.inj h
    | Err _ => cases h
  | Err x => cases b with
    | Ok _ => cases h
    | Err y => cases x; cases y; rfl

theorem encoded_result_injective
    (a b : core.result.Result (Slice U8) RustCryptoUnpadding.Error)
    (ha : ∀ message ∈ forgetResult a, message.length ≤ 16)
    (hb : ∀ message ∈ forgetResult b, message.length ≤ 16)
    (heq : encodeOption (forgetResult a) = encodeOption (forgetResult b)) : a = b := by
  exact forgetResult_injective (encodeOption_injective _ _ ha hb heq)

end LibSignalReference.Proofs.Unpad
