import TlsMpc.Node.Flows.Ceremony

/-!
# Well-formedness of the ceremony scripts (ops 80, 81)

`secretsScript_wf`: op 80 is well formed from every context in which no id from `n` on was ever
defined and `ceremony-secrets` has its declared signature. `registerScript_wf`: op 81's engine part
is well formed from every context in which the two handles are live, below `n`, with op 80's marks
(private, not once), and the ids from `n` are fresh.
-/

namespace TlsMpc.Node.Flows.Ceremony

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts

/-- An input of `w` private bits, not once (`check`'s `boolInputBoth` with `rev = false`). -/
def inInfo (w : Nat) : BoolInfo := ⟨List.replicate w (Mark.ofInput false), false⟩

/-- A private handle of `w` bits, not once (op 80's password and recovery). -/
def privInfo (w : Nat) : BoolInfo := ⟨List.replicate w .never, false⟩

theorem useBools_keepAll' (c : Ctx) (f : BoolH → BoolInfo) :
    ∀ hs : List BoolH, (∀ h ∈ hs, c.bool? h = some (f h) ∧ (f h).once = false) →
      c.useBools hs = some (hs.map f, c)
  | [], _ => useBools_nil c
  | h :: hs, hh => by
    have h0 := hh h (by simp)
    exact useBools_cons (useBool_keep h0.1 h0.2) (useBools_keepAll' c f hs fun g hg => hh g (by simp [hg]))

theorem seenB_push (c : Ctx) (n : Nat) (i : BoolInfo) : (push c n i).seenB = n :: c.seenB := rfl

theorem secretsScript_wf (sigs : Bytes → Option Sig) (c : Ctx) (n seedSlot maskSlot recoverySlot : Nat)
    (hf : Fresh c n) (hsig : sigs secretsName = some ⟨8 * inputBytes, secretsMarks⟩) :
    WF sigs c (secretsScript n seedSlot maskSlot recoverySlot) := by
  unfold secretsScript
  simp only [inputBlock, kernelBlock, List.cons_append, List.nil_append, seqs_cons]
  -- the three inputs
  refine WF_seq sigs _ _ _ _ (check_boolInputBoth sigs hf (8 * seedBytes) false false (by decide)) ?_
  have f1 := (hf.push n (Nat.le_refl n) (inInfo (8 * seedBytes))).push (n + 1) (Nat.le_refl _) (inInfo (8 * seedBytes))
  refine WF_seq sigs _ _ _ _ (check_boolInputBoth sigs f1 (8 * passwordBytes) false false (by decide)) ?_
  have f2 := (f1.push (n + 2) (Nat.le_refl _) (inInfo (8 * passwordBytes))).push (n + 3) (Nat.le_refl _)
    (inInfo (8 * passwordBytes))
  refine WF_seq sigs _ _ _ _ (check_boolInputBoth sigs f2 (8 * recoveryBytes) false false (by decide)) ?_
  have f3 := (f2.push (n + 4) (Nat.le_refl _) (inInfo (8 * recoveryBytes))).push (n + 5) (Nat.le_refl _)
    (inInfo (8 * recoveryBytes))
  -- the concatenation
  let c3 := push (push (push (push (push (push c n (inInfo (8 * seedBytes))) (n + 1) (inInfo (8 * seedBytes)))
    (n + 2) (inInfo (8 * passwordBytes))) (n + 3) (inInfo (8 * passwordBytes))) (n + 4) (inInfo (8 * recoveryBytes)))
    (n + 5) (inInfo (8 * recoveryBytes))
  let f : BoolH → BoolInfo := fun h =>
    if h.id < n + 2 then inInfo (8 * seedBytes) else if h.id < n + 4 then inInfo (8 * passwordBytes)
    else inInfo (8 * recoveryBytes)
  have hu : c3.useBools [⟨n⟩, ⟨n + 1⟩, ⟨n + 2⟩, ⟨n + 3⟩, ⟨n + 4⟩, ⟨n + 5⟩] =
      some ([⟨n⟩, ⟨n + 1⟩, ⟨n + 2⟩, ⟨n + 3⟩, ⟨n + 4⟩, ⟨n + 5⟩].map f, c3) := by
    refine useBools_keepAll' c3 f _ (fun h hh => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [c3, f, bool?_push, inInfo]
  have hlen : (([⟨n⟩, ⟨n + 1⟩, ⟨n + 2⟩, ⟨n + 3⟩, ⟨n + 4⟩, ⟨n + 5⟩] : List BoolH).map f |>.map (·.marks)).flatten.length =
      8 * inputBytes := by
    simp [f, inInfo, inputBytes, seedBytes, passwordBytes, recoveryBytes, -List.reduceReplicate]
  have hconcat := check_concat sigs (n := n + 6) hu f3 (by rw [hlen]; decide)
  refine WF_seq sigs _ _ _ _ hconcat ?_
  -- the kernel
  have honce : (([⟨n⟩, ⟨n + 1⟩, ⟨n + 2⟩, ⟨n + 3⟩, ⟨n + 4⟩, ⟨n + 5⟩] : List BoolH).map f).any (·.once) = false := by
    simp [f, inInfo]
  have f4 := f3.push (n + 6) (Nat.le_refl _) ⟨(([⟨n⟩, ⟨n + 1⟩, ⟨n + 2⟩, ⟨n + 3⟩, ⟨n + 4⟩, ⟨n + 5⟩] : List BoolH).map f
      |>.map (·.marks)).flatten, (([⟨n⟩, ⟨n + 1⟩, ⟨n + 2⟩, ⟨n + 3⟩, ⟨n + 4⟩, ⟨n + 5⟩] : List BoolH).map f).any (·.once)⟩
  refine WF_seq sigs _ _ _ _ (check_run sigs (n := n + 7) hsig Nat.one_pos
    (useBool_keep (bool?_push_self _ _ _) honce) (by rw [hlen, Nat.one_mul]) f4 (by decide)
    (by simp [secretsMarks, passwordBytes, recoveryBytes, maxWidth, -List.reduceReplicate])) ?_
  -- the three slices
  have f5 := f4.push (n + 7) (Nat.le_refl _) ⟨(List.replicate 1 secretsMarks).flatten, false⟩
  have hout : (⟨(List.replicate 1 secretsMarks).flatten, false⟩ : BoolInfo).marks.length = 8 * outputBytes := by
    simp [secretsMarks, outputBytes, passwordBytes, recoveryBytes, -List.reduceReplicate]
  refine WF_seq sigs _ _ _ _ (check_slice sigs (n := n + 8) (useBool_keep (bool?_push_self _ _ _) rfl)
    (by rw [hout]; simp [outputBytes, passwordBytes, recoveryBytes]) f5 (by decide)) ?_
  have f6 := f5.push (n + 8) (Nat.le_refl _) ⟨((List.replicate 1 secretsMarks).flatten.drop 0).take
    (8 * passwordBytes - 0), false⟩
  refine WF_seq sigs _ _ _ _ (check_slice sigs (n := n + 9)
    (useBool_keep (by rw [bool?_push_of_ne _ _ _ _ (by simp)]; exact bool?_push_self _ _ _) rfl)
    (by rw [hout]; simp [outputBytes, passwordBytes, recoveryBytes]) f6 (by decide)) ?_
  have f7 := f6.push (n + 9) (Nat.le_refl _) ⟨((List.replicate 1 secretsMarks).flatten.drop (8 * passwordBytes)).take
    (8 * (passwordBytes + recoveryBytes) - 8 * passwordBytes), false⟩
  refine WF_seq sigs _ _ _ _ (check_slice sigs (n := n + 10)
    (useBool_keep (i := ⟨(List.replicate 1 secretsMarks).flatten, false⟩) (by simp [bool?_push]) rfl)
    (by rw [hout]; simp [outputBytes, passwordBytes, recoveryBytes]) f7 (by decide)) ?_
  -- the frees
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by simp [c3, bool?_push])) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by simp [c3, bool?_push, bool?_drop])) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by simp [c3, bool?_push, bool?_drop])) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by simp [c3, bool?_push, bool?_drop])) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by simp [c3, bool?_push, bool?_drop])) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by simp [c3, bool?_push, bool?_drop])) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by simp [c3, bool?_push, bool?_drop])) ?_
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by simp [c3, bool?_push, bool?_drop])) ?_
  -- the opening of `masked`
  have hm : ((List.replicate 1 secretsMarks).flatten.drop (8 * (passwordBytes + recoveryBytes))).take
      (8 * outputBytes - 8 * (passwordBytes + recoveryBytes)) = List.replicate (8 * passwordBytes) .pub := by
    simp only [List.replicate_one, List.flatten_singleton, secretsMarks]
    rw [List.drop_left' (by simp [passwordBytes, recoveryBytes, -List.reduceReplicate])]
    simp [outputBytes, passwordBytes, recoveryBytes, -List.reduceReplicate]
  apply WF_openThen
  rw [check_openBool sigs (i := ⟨((List.replicate 1 secretsMarks).flatten.drop (8 * (passwordBytes + recoveryBytes))).take
      (8 * outputBytes - 8 * (passwordBytes + recoveryBytes)), false⟩) (by decide)
    (useBool_keep (by simp [c3, bool?_push, bool?_drop]) rfl) (by rw [hm]; simp [Mark.openable, -List.reduceReplicate])]
  intro b _
  unfold afterMasked
  simp only [seqs_cons, seqs_nil]
  refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by simp [c3, bool?_push, bool?_drop])) ?_
  split
  · exact WF.done _ _
  · exact WF.abort _ _

/-- **Op 81's engine part is well formed** from a context in which the password and recovery
handles are live, below `n`, with op 80's marks, and no id from `n` on was defined. -/
theorem registerScript_wf (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (password recovery : BoolH) (tail : B8)
    (hf : Fresh c n) (hpn : password.id < n) (hrn : recovery.id < n) (hne : password.id ≠ recovery.id)
    (hp : c.bool? password = some (privInfo (8 * passwordBytes)))
    (hr : c.bool? recovery = some (privInfo (8 * recoveryBytes))) :
    WF sigs c (registerScript n password recovery tail) := by
  unfold registerScript
  split
  · next htl =>
    unfold registerBlock
    split
    · simp only [seqs_cons, seqs_nil]
      have hu : c.useBools [password, recovery] = some ([privInfo (8 * passwordBytes), privInfo (8 * recoveryBytes)], c) :=
        useBools_cons (useBool_keep hp rfl) (useBools_cons (useBool_keep hr rfl) (useBools_nil c))
      refine WF_seq sigs _ _ _ _ (check_concat sigs (n := n + 1) hu (hf.mono (by omega))
        (by simp [privInfo, passwordBytes, recoveryBytes, maxWidth, -List.reduceReplicate])) ?_
      have a1 : password.id ≠ n + 1 := by omega
      have a2 : recovery.id ≠ n + 1 := by omega
      refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by simp [bool?_push, a1, hp])) ?_
      refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by simp [bool?_push, bool?_drop, a2, hne.symm, hr])) ?_
      exact WF.done _ _
    · simp only [seqs_cons, seqs_nil]
      have hl : (bitsOf tail).length ≤ maxWidth := by simp [maxWidth]; omega
      refine WF_seq sigs _ _ _ _ (check_boolPublic sigs hf _ hl) ?_
      have b1 : password.id ≠ n := by omega
      have b2 : recovery.id ≠ n := by omega
      have hu : (push c n ⟨List.replicate (bitsOf tail).length .pub, false⟩).useBools [⟨n⟩, password, recovery] =
          some ([⟨List.replicate (bitsOf tail).length .pub, false⟩, privInfo (8 * passwordBytes),
            privInfo (8 * recoveryBytes)], push c n ⟨List.replicate (bitsOf tail).length .pub, false⟩) :=
        useBools_cons (useBool_keep (bool?_push_self _ _ _) rfl)
          (useBools_cons (useBool_keep (by rw [bool?_push_of_ne _ _ _ _ b1]; exact hp) rfl)
            (useBools_cons (useBool_keep (by rw [bool?_push_of_ne _ _ _ _ b2]; exact hr) rfl) (useBools_nil _)))
      refine WF_seq sigs _ _ _ _ (check_concat sigs (n := n + 1) hu (hf.push n (Nat.le_refl n) _)
        (by simp [privInfo, passwordBytes, recoveryBytes, maxWidth, -List.reduceReplicate]; omega)) ?_
      have a1 : password.id ≠ n + 1 := by omega
      have a2 : recovery.id ≠ n + 1 := by omega
      refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by simp [bool?_push])) ?_
      refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by simp [bool?_push, bool?_drop, a1, b1, hp])) ?_
      refine WF_seq sigs _ _ _ _ (check_freeBool' sigs (by simp [bool?_push, bool?_drop, a2, b2, hne.symm, hr])) ?_
      exact WF.done _ _
  · exact WF.abort _ _

end TlsMpc.Node.Flows.Ceremony
