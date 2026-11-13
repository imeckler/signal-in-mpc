import TlsMpc.Node.Policy.ReceiveReply

/-!
# The upgrade response's head (proof track P1, item 5)

New file; it changes no definition. No emitter or executable imports it. Standard axioms only.

`ReceiveProofs.T1` is about the stream after the upgrade (`classifyFrames`). Before it, the controller
reveals the HTTP upgrade response's head in runs of `budget s = 4 - min terminator 3` bytes, counting in
`State.terminator` how many bytes of CR LF CR LF the revealed bytes end with. This file proves that
nothing past the head is revealed that way:

* **`head_run`** (reference side): if the bytes `S` revealed so far contain no CR LF CR LF, every byte
  of the next `4 - k` (`k` the count after `S`, `Head.after 0 S`) is `head` in `ReceiveSpec.classify`,
  whatever those bytes and whatever follows: the head cannot end sooner.
* **`frameByte_terminator`** (controller side): before the upgrade, `frameByte` advances
  `State.terminator` exactly as the reference's matcher does (`ReceiveStream.Head.next`), and sets
  `upgraded` exactly when it reaches 4 (the upgrade parser must agree, else the byte is refused).
* **`budget_head`**: before the upgrade the run is `4 - min terminator 3` bytes.

Together: while `upgraded` is false and `terminator = Head.after 0 S` (`S` the revealed bytes, no
terminator in them), the controller's next run lies inside the head (`head_run`); at the byte that
completes CR LF CR LF it is upgraded, and from there on `classifyFrames` takes over
(`ReceiveSpec.classify` = `fill .head (take n) ++ classifyFrames (drop n)`).

Not here: that `payloadByte` (the message side of `step`) leaves `upgraded` and `terminator` alone
(it never assigns them; a keeping lemma like `frameByte_keeps` for those two fields), and the
record loop's composition of the above.
-/

open TlsMpc

namespace ReceiveHead

open PublicReceive ReceiveProofs
open ReceiveSpec (Class fill headLength classify)
open ReceiveStream (Head.next Head.find)

/-- The matcher's count after a list of bytes, from count `k`. -/
def after (k : Nat) : List Byte → Nat
  | [] => k
  | b :: rest => after (Head.next k b) rest

theorem next_le (k : Nat) (b : Byte) : Head.next k b ≤ k + 1 := by
  unfold Head.next
  generalize (if k % 2 = 0 then (13 : Byte) else 10) = e
  by_cases h1 : b = e
  · rw [if_pos h1]; omega
  · rw [if_neg h1]; split <;> omega

theorem find_append : ∀ (k : Nat) (S W : List Byte), Head.find k S = none →
    Head.find k (S ++ W) = (Head.find (after k S) W).map (· + S.length)
  | k, [], W, _ => by simp [after]
  | k, b :: S, W, h => by
    simp only [Head.find] at h
    by_cases h4 : Head.next k b = 4
    · rw [if_pos h4] at h; cases h
    rw [if_neg h4] at h
    have hS : Head.find (Head.next k b) S = none := by
      cases e : Head.find (Head.next k b) S with
      | none => rfl
      | some n => rw [e] at h; cases h
    rw [List.cons_append, Head.find, if_neg h4, find_append _ S W hS]
    simp only [after, List.length_cons, Option.map_map]
    cases Head.find (after (Head.next k b) S) W <;> simp [Function.comp_def, Nat.add_assoc]

theorem find_ge : ∀ (W : List Byte) (k n : Nat), k ≤ 3 → Head.find k W = some n → 4 - k ≤ n
  | [], _, _, _, h => by simp [Head.find] at h
  | b :: W, k, n, hk, h => by
    simp only [Head.find] at h
    have hle := next_le k b
    by_cases h4 : Head.next k b = 4
    · rw [if_pos h4] at h; cases h; omega
    rw [if_neg h4] at h
    cases e : Head.find (Head.next k b) W with
    | none => rw [e] at h; cases h
    | some n' =>
      rw [e] at h
      simp only [Option.map_some, Option.some.injEq] at h
      have := find_ge W (Head.next k b) n' (by omega) e
      omega

theorem after_le : ∀ (k : Nat) (S : List Byte), k ≤ 3 → Head.find k S = none → after k S ≤ 3
  | k, [], hk, _ => hk
  | k, b :: S, hk, h => by
    simp only [Head.find] at h
    have hle := next_le k b
    by_cases h4 : Head.next k b = 4
    · rw [if_pos h4] at h; cases h
    rw [if_neg h4] at h
    have hS : Head.find (Head.next k b) S = none := by
      cases e : Head.find (Head.next k b) S with
      | none => rfl
      | some n => rw [e] at h; cases h
    exact after_le _ S (by omega) hS

/-- **The head cannot end within the next `4 - k` bytes.** If the bytes `S` revealed so far contain no
CR LF CR LF, every one of the next `4 - after 0 S` bytes of the stream, whatever they and the bytes
after them are, is `head` in the reference. -/
theorem head_run (ob : Bool) (S : List Byte) (hS : Head.find 0 S = none) (Y Z : List Byte)
    (hY : Y.length ≤ 4 - after 0 S) (i : Nat) (hi : i < Y.length) :
    (classify ob (S ++ (Y ++ Z)))[S.length + i]? = some .head := by
  have hk := after_le 0 S (by omega) hS
  unfold classify
  rw [ReceiveStream.Head.headLength_eq, find_append 0 S _ hS]
  cases e : Head.find (after 0 S) (Y ++ Z) with
  | none =>
    exact ReceiveReply.fill_get _ _ _ (by simp; omega)
  | some n =>
    have := find_ge (Y ++ Z) (after 0 S) n hk e
    dsimp only [Option.map_some]
    rw [List.getElem?_append_left (by rw [ReceiveReply.fillL, List.length_take]; simp; omega)]
    exact ReceiveReply.fill_get _ _ _ (by rw [List.length_take]; simp; omega)

/-! ### The controller's count -/

theorem terminator_next (t : Nat) (byte : Byte) :
    (if byte == (if t % 2 == 0 then (13 : Byte) else 10) then t + 1 else if byte == 13 then 1 else 0) =
      Head.next t byte := by
  unfold Head.next
  by_cases h2 : t % 2 = 0
  · simp only [h2, beq_self_eq_true, if_true]
    by_cases hb : byte = 13
    · simp [hb]
    · simp
  · have : (t % 2 == 0) = false := by simp [h2]
    simp only [this, h2, Bool.false_eq_true, if_false]
    by_cases hb : byte = 10
    · simp [hb]
    · by_cases hb13 : byte = 13
      · simp [hb13]
      · simp

/-- `frameByte`'s upgrade part, before the upgrade: the count is the reference matcher's, and the
connection is upgraded exactly when it reaches 4. -/
theorem upgradePart_terminator {s s1 : State} {byte a : Byte} (hu : s.upgraded = false)
    (h : upgradePart s byte = .ok (a, s1)) :
    s1.terminator = Head.next s.terminator byte ∧ (s1.upgraded = true ↔ Head.next s.terminator byte = 4) := by
  unfold upgradePart at h
  simp only [hu, Bool.false_eq_true, ↓reduceIte] at h
  generalize TlsWebSocketUpgrade.runByte PublicReceive.fast (s.upgrade ++ s.accept ++ [on, byte]) = out at h
  by_cases g0 : (PublicReceive.get out 0 == on) = true
  case neg => simp only [g0, Bool.false_eq_true, ↓reduceIte, throw_bind_ex, throw_ok_iff] at h
  simp only [g0, ↓reduceIte, pure_bind] at h
  rw [terminator_next] at h
  by_cases hc : ((PublicReceive.get out 1 == on) == (Head.next s.terminator byte == 4)) = true
  · rw [if_pos hc] at h
    cases h
    refine ⟨rfl, ?_⟩
    have hc' : (PublicReceive.get out 1 == on) = (Head.next s.terminator byte == 4) := beq_iff_eq.mp hc
    show (PublicReceive.get out 1 == on) = true ↔ _
    rw [hc', beq_iff_eq]
  · rw [if_neg hc] at h
    simp only [throw_bind_ex, throw_ok_iff] at h

theorem frameRest_upgrade {s s2 : State} {byte a : Byte} {ev : List Byte} (h : frameRest s byte a = .ok (s2, ev)) :
    s2.terminator = s.terminator ∧ s2.upgraded = s.upgraded := by
  unfold frameRest at h
  by_cases g1 : (s.skip == 0) = true
  case neg => simp only [g1, Bool.false_eq_true, ↓reduceIte, throw_bind_ex, throw_ok_iff] at h
  simp only [g1, ↓reduceIte, pure_bind] at h
  by_cases g2 : (s.pending && s.message.isEmpty && PublicReceive.get s.frame 0 == on) = true
  · simp only [g2, ↓reduceIte] at h
    generalize TlsWebSocketFrame.runByte PublicReceive.fast capacity (s.frame ++ [a, byte]) = F at h
    by_cases g3 : (PublicReceive.get F 0 == on) = true
    case neg => simp only [g3, Bool.false_eq_true, ↓reduceIte, throw_bind_ex, throw_ok_iff] at h
    simp only [g3, ↓reduceIte] at h
    cases h
    exact ⟨rfl, rfl⟩
  · simp only [g2, Bool.false_eq_true, ↓reduceIte] at h
    generalize TlsWebSocketFrame.runByte PublicReceive.fast capacity (s.frame ++ [a, byte]) = F at h
    by_cases g3 : (PublicReceive.get F 0 == on) = true
    case neg => simp only [g3, Bool.false_eq_true, ↓reduceIte, throw_bind_ex, throw_ok_iff] at h
    simp only [g3, ↓reduceIte] at h
    cases h
    exact ⟨rfl, rfl⟩

/-- **Before the upgrade, `frameByte` counts CR LF CR LF as the reference does**, and upgrades exactly
when the count reaches 4. -/
theorem frameByte_terminator {s s1 : State} {b : Byte} {ev : List Byte} (hu : s.upgraded = false)
    (h : frameByte s b = .ok (s1, ev)) :
    s1.terminator = Head.next s.terminator b ∧ (s1.upgraded = true ↔ Head.next s.terminator b = 4) := by
  rw [frameByte_split, frameUpgrade_eq, bind_ok_iff] at h
  obtain ⟨⟨a, s0⟩, h1, h2⟩ := h
  obtain ⟨t1, t2⟩ := upgradePart_terminator hu h1
  obtain ⟨r1, r2⟩ := frameRest_upgrade h2
  exact ⟨r1.trans t1, by rw [r2]; exact t2⟩

/-- Before the upgrade, the run is `4 - min terminator 3` bytes. -/
theorem budget_head (s : State) (hu : s.upgraded = false) : budget s = 4 - min s.terminator 3 := by
  unfold budget; simp [hu]

/-- **Item 5, composed for one run.** Before the upgrade, with the controller's count equal to the
reference matcher's over the revealed bytes `S` (no CR LF CR LF among them), every byte of the run the
controller reveals (`budget s` bytes, whatever they are) is `head` in `ReceiveSpec.classify`. -/
theorem upgrade_run_safe (ob : Bool) {s : State} (hu : s.upgraded = false) (S : List Byte)
    (hS : Head.find 0 S = none) (ht : s.terminator = after 0 S) (Y Z : List Byte) (hY : Y.length ≤ budget s)
    (i : Nat) (hi : i < Y.length) : (classify ob (S ++ (Y ++ Z)))[S.length + i]? = some .head := by
  have hk := after_le 0 S (by omega) hS
  rw [budget_head s hu, ht, Nat.min_eq_left hk] at hY
  exact head_run ob S hS Y Z hY i hi

end ReceiveHead
