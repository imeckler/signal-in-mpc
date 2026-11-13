import TlsMpc.Node.Flows.MasksWF
import TlsMpc.Node.Flows.Convert

/-!
# Well-formedness of the conversion scripts (the shell's `check` admits them)

Stage S10. With the machinery of `MasksWF.lean`:

  * `sharedBits_wf`: `Convert.sharedBits f0 n slot` passes `check` on every branch, from any context
    in which the 5·n field ids from `f0` were never defined and the programs `field-bit-check` and
    `field-bit-xor` are loaded with their signatures, for `0 < n` and `2·n` within the width limit.

The `_wf` theorems of `wordToField`, `fieldToWord`, `bitsToField` and `Account.openStep` are not
proved here (the test vectors admit every batch of the test instance).
-/

namespace TlsMpc.Node.Flows.Convert

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts (seq seqs openThen frees WFP_seq)
open TlsMpc.Node.Flows.Run
open TlsMpc.Node.Flows.Conv
open TlsMpc.Node.Flows.Masks (defBlock defFields_two check_fieldInput' check_program' check_openField'
  WFP_openFieldThen flatten_replicate_singleton length_flatMap_const)
open TlsMpc.FieldDag (F modulus ofNat)

theorem sharedBits_wf (sigs : Bytes → Option Sig) (c : Ctx) (f0 n slot : Nat) (hn : 0 < n)
    (hw : 2 * n ≤ maxWidth) (hfresh : ∀ j, f0 ≤ j → j < f0 + 5 * n → j ∉ c.seenF)
    (hp1 : c.progs bitCheckName = some ⟨1, 0, [.pub]⟩) (hp2 : c.progs bitXorName = some ⟨2, 0, [.never]⟩) :
    WF sigs c (sharedBits f0 n slot) := by
  suffices h : WFP sigs (fun _ _ => True) c (sharedBits f0 n slot) from h.wf
  -- the inputs
  obtain ⟨c1, d1, b1, s1, p1, e1, n1⟩ := defBlock c (fun i => (⟨f0 + i⟩ : FieldH)) f0 n (Mark.ofInput false)
    (fun _ _ => rfl) (fun j hj1 hj2 => hfresh j hj1 (by omega))
  obtain ⟨c2, d2, b2, s2, p2, e2, n2⟩ := defBlock c1 (fun i => (⟨f0 + n + i⟩ : FieldH)) (f0 + n) n
    (Mark.ofInput false) (fun _ _ => rfl) (fun j hj1 hj2 hmem => by
      rcases (n1 j).mp hmem with h' | h'
      · exact hfresh j (by omega) (by omega) h'
      · omega)
  have hin : ∀ g ∈ bitsA f0 n ++ bitsB f0 n, c2.field? g = some (Mark.ofInput false) := by
    intro g hg
    simp only [bitsA, bitsB, List.mem_append, List.mem_map, List.mem_range] at hg
    rcases hg with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · have h2 := e2 ⟨f0 + i⟩
      have h1 := e1 ⟨f0 + i⟩
      dsimp only at h1 h2
      rw [h2, if_neg (by omega), h1, if_pos (by omega)]
    · have h2 := e2 ⟨f0 + n + i⟩
      dsimp only at h2
      rw [h2, if_pos (by omega)]
  unfold sharedBits
  refine WFP_seq sigs c c2 _ _ (check_fieldInput' sigs c c2 _ _ _ _
    (by rw [bitsA, bitsB, List.length_map, List.length_map])
    (defFields_two c c1 c2 _ _ n _ (by rw [bitsA, List.length_map, List.length_range])
      (by rw [bitsB, List.length_map, List.length_range]) d1 d2)) ?_
  -- the bit checks
  obtain ⟨c3, d3, b3, s3, p3, e3, n3⟩ := defBlock c2 (fun i => (⟨f0 + 2 * n + i⟩ : FieldH)) (f0 + 2 * n) (2 * n)
    .pub (fun _ _ => rfl) (fun j hj1 hj2 hmem => by
      rcases (n2 j).mp hmem with h' | h'
      · rcases (n1 j).mp h' with h'' | h''
        · exact hfresh j (by omega) (by omega) h''
        · omega
      · omega)
  refine WFP_seq sigs c2 c3 _ _ (check_program' sigs c2 c3 bitCheckName (2 * n) (bitsA f0 n ++ bitsB f0 n)
    (bitsChk f0 n) Label.scalarBitChecks ⟨1, 0, [.pub]⟩ (by decide) (by rw [p2, p1]; exact hp1) rfl (by omega) hw
    (by
      rw [List.length_append, bitsA, bitsB, List.length_map, List.length_map, List.length_range]
      show n + n = 2 * n * 1
      omega)
    (by
      rw [bitsChk, List.length_map, List.length_range]
      show 2 * n = 2 * n * 1
      omega)
    (fun g hg => by rw [hin g hg]; rfl)
    (by
      show c2.defFields ((List.range (2 * n)).map fun i => (⟨f0 + 2 * n + i⟩ : FieldH))
        (List.replicate (2 * n) [Mark.pub]).flatten = some c3
      rw [flatten_replicate_singleton]
      exact d3)) ?_
  -- the opening
  refine WFP_openFieldThen sigs c3 c3 _ _ _ _ (check_openField' sigs c3 _ _ (by decide) (fun x hx => ?_))
    (fun z _ => ?_)
  · simp only [bitsChk, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    have h3 := e3 ⟨f0 + 2 * n + i⟩
    dsimp only at h3
    exact ⟨.pub, by rw [h3, if_pos (by omega)], rfl⟩
  split
  · -- the XOR
    obtain ⟨c4, d4, -⟩ := defBlock c3 (fun i => (⟨f0 + 4 * n + i⟩ : FieldH)) (f0 + 4 * n) n .never
      (fun _ _ => rfl) (fun j hj1 hj2 hmem => by
        rcases (n3 j).mp hmem with h' | h'
        · rcases (n2 j).mp h' with h'' | h''
          · rcases (n1 j).mp h'' with h3 | h3
            · exact hfresh j (by omega) (by omega) h3
            · omega
          · omega
        · omega)
    refine WFP_seq sigs c3 c4 _ _ (check_program' sigs c3 c4 bitXorName n (bitsPairs f0 n) (bitsOuts f0 n)
      Label.scalarBitChecks ⟨2, 0, [.never]⟩ (by decide) (by rw [p3, p2, p1]; exact hp2) rfl hn
      (Nat.le_trans (Nat.le_mul_of_pos_left n (by decide)) hw)
      (by
        rw [bitsPairs, length_flatMap_const _ 2 _ (fun i _ => rfl), List.length_range])
      (by
        rw [bitsOuts, List.length_map, List.length_range]
        show n = n * 1
        omega)
      (fun g hg => by
        simp only [bitsPairs, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hg
        obtain ⟨i, hi, hg | hg⟩ := hg
        · subst hg
          have h3 := e3 ⟨f0 + i⟩
          dsimp only at h3
          rw [h3, if_neg (by omega), hin ⟨f0 + i⟩ (by
            simp only [bitsA, List.mem_append, List.mem_map, List.mem_range]
            exact Or.inl ⟨i, hi, rfl⟩)]
          rfl
        · subst hg
          have h3 := e3 ⟨f0 + n + i⟩
          dsimp only at h3
          rw [h3, if_neg (by omega), hin ⟨f0 + n + i⟩ (by
            simp only [bitsB, List.mem_append, List.mem_map, List.mem_range]
            exact Or.inr ⟨i, hi, rfl⟩)]
          rfl)
      (by
        show c3.defFields ((List.range n).map fun i => (⟨f0 + 4 * n + i⟩ : FieldH))
          (List.replicate n [Mark.never]).flatten = some c4
        rw [flatten_replicate_singleton]
        exact d4)) ?_
    exact WFP.done _ _ trivial
  · exact WFP.abort _ _

end TlsMpc.Node.Flows.Convert
