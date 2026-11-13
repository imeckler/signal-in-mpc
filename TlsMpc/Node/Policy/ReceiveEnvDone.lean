import TlsMpc.Node.Policy.ReceiveEnvelope
import TlsMpc.Node.Policy.ReceiveStream

/-!
# T1, item 3: a walked envelope has no `error` in it

New file; it changes no definition. No emitter or executable imports it. Standard axioms only.

`ReceiveProofs.envelope_payload_unrevealed` says every byte the envelope walk (`envWalk`) reveals is
public in the reference (`ReceiveSpec.envelope`). Here: every byte the walk *covers*, revealed or
passed over, is not `error` (`envWalk_noErr`, the same induction as `envWalk_safe`: the walk stops at
the byte after which the reference's classes become `error`, a bad wire type or the 10th byte of a
varint). So once the controller has walked a whole delivered envelope without refusing a byte, the
envelope's classes have no `error` (`envelope_noErr`): the hypothesis `NoErr (requestBody path B)` of
`ReceiveRequestScan.qshape_skip` for a `/api/v1/message` body.
-/

open TlsMpc

namespace ReceiveEnvDone

open PublicReceive ReceiveProofs
open ReceiveSpec (Class fill varintThen varintEnd varintValue)

/-- No position the walk covers is `error`. -/
def NE (R : List Bool) (C : List Class) : Prop := ∀ i, i < R.length → C[i]? ≠ some .error

theorem ne_nil (C : List Class) : NE [] C := fun _ h => absurd h (Nat.not_lt_zero _)

theorem ne_append {R1 R2 : List Bool} {C1 C2 : List Class} (h1 : NE R1 C1) (hl : R1.length = C1.length)
    (h2 : NE R2 C2) : NE (R1 ++ R2) (C1 ++ C2) := by
  intro i hi
  by_cases hlt : i < R1.length
  · rw [List.getElem?_append_left (by omega)]; exact h1 i hlt
  · rw [List.getElem?_append_right (by omega), ← hl]
    exact h2 _ (by simp only [List.length_append] at hi; omega)

theorem ne_rep {α : Type} (b : Bool) (n : Nat) (T : List α) (hn : n ≤ T.length) (c : Class) (hc : c ≠ .error)
    (C : List Class) : NE (List.replicate n b) (fill c T ++ C) := by
  intro i hi
  simp only [List.length_replicate] at hi
  rw [List.getElem?_append_left (by simp [fill]; omega)]
  simp only [fill, List.getElem?_map, List.getElem?_eq_getElem (show i < T.length by omega), Option.map_some,
    ne_eq, Option.some.injEq]
  exact hc

theorem ne_fill {α : Type} (b : Bool) (n : Nat) (T : List α) (hn : n ≤ T.length) (c : Class) (hc : c ≠ .error) :
    NE (List.replicate n b) (fill c T) := by
  simpa using ne_rep b n T hn c hc []

/-- The induction hypothesis: the walk covers no `error`, from any field boundary, on bytes shorter than
`fuel`. -/
def WalkNE (fuel : Nat) : Prop := ∀ (E H : List Byte) (s c : Nat), HdrOK H s c → E.length < fuel →
  NE (envWalk H s 0 E) (ReceiveSpec.envelope fuel E)

theorem value_tail_ne {fuel : Nat} (ih : WalkNE fuel) {H kv after : List Byte} {s c k : Nat} (hH : HdrOK H s c)
    (hk : Varint kv k) (hk10 : kv.length ≤ 10) (hw : k % 8 = 0 ∨ k % 8 = 2)
    (hlen : kv.length + after.length < fuel + 1)
    (hcomplete : ∀ vv v, Varint vv v → vv.length ≤ 10 →
      HdrOK (H ++ (kv ++ vv)) s c ∧ ∀ p, s ≤ p → (envelopeScan (H ++ (kv ++ vv)) p).1 = .more true) :
    NE (envWalk (H ++ kv) s 0 after) (varintThen after fun _ rest => ReceiveSpec.envelope fuel rest) := by
  rcases varintEnd_cases 10 after with ⟨m2, he, h1, h2, h3, hv⟩ | ⟨he, hl, hu⟩ | ⟨he, hl, hu⟩
  · rw [varintThen_done he]
    generalize hrest : after.drop m2 = rest
    generalize hvv : after.take m2 = vv at hv
    have hafter : after = vv ++ rest := by rw [← hvv, ← hrest, List.take_append_drop]
    have hvl : vv.length = m2 := by rw [← hvv]; simp; omega
    have hv10 : vv.length ≤ 10 := by omega
    subst hafter
    obtain ⟨hH', hq⟩ := hcomplete vv _ hv hv10
    rw [walk_more vv (H ++ kv) rest (fun j h1 h2 => by
      by_cases hj : j < vv.length
      · refine ⟨false, ?_⟩
        rw [List.append_assoc]
        exact val_more hH hk hk10 hw (varint_prefix hv j hj) (by simp; omega)
      · refine ⟨true, ?_⟩
        rw [show j = vv.length by omega, List.take_length, List.append_assoc]
        exact hq s (Nat.le_refl s))]
    refine ne_append (ne_fill true _ vv (Nat.le_refl _) _ (by decide)) (by simp [fill_length]) ?_
    rw [List.append_assoc]
    exact ih _ _ s c hH' (by simp at hlen; omega)
  · rw [varintThen_short he, valrun_short hH hk hk10 hw hl hu]
    exact ne_fill true _ after (Nat.le_refl _) _ (by decide)
  · rw [varintThen_tooLong he, valrun_tooLong hH hk hk10 hw hl hu]
    exact ne_rep true 10 (after.take 10) (by simp; omega) _ (by decide) _

theorem walk_case0_ne {fuel : Nat} (ih : WalkNE fuel) {H kv after : List Byte} {s c k : Nat} (hH : HdrOK H s c)
    (hk : Varint kv k) (hk10 : kv.length ≤ 10) (hw : k % 8 = 0) (hlen : (kv ++ after).length < fuel + 1) :
    NE (envWalk H s 0 (kv ++ after)) (fill .structure kv ++ envNext fuel k after) := by
  have hne := varint_ne_nil hk
  rw [walk_key hH hk hk10 (Or.inl hw)]
  have hn : envNext fuel k after = varintThen after (fun _ rest => ReceiveSpec.envelope fuel rest) := by
    unfold envNext; rw [hw]; rfl
  rw [hn]
  refine ne_append (ne_fill true _ kv (Nat.le_refl _) _ (by decide)) (by simp [fill_length]) ?_
  exact value_tail_ne ih hH hk hk10 (Or.inl hw) (by simpa using hlen)
    (fun vv v hv hv10 => field_complete hH (Nat.le_refl s) (by simp; have := varint_ne_nil hv; omega)
      (round_varint (H := H) hk hk10 hw hv hv10))

theorem payload_tail_ne {fuel : Nat} (ih : WalkNE fuel) {H F after : List Byte} {s c' n : Nat} (hn : 0 < n)
    (hcomplete : HdrOK (H ++ F) (s + 1) c' ∧ ∀ p, s + 1 ≤ p → (envelopeScan (H ++ F) p).1 = .more true)
    (hlen : after.length < fuel + n) :
    NE (envWalk (H ++ F) s n after)
      (fill Class.envelope (after.take n) ++ ReceiveSpec.envelope fuel (after.drop n)) := by
  by_cases hs : after.length < n
  · rw [walk_pass_short n after hn hs]
    exact ne_rep false _ (after.take n) (by simp; omega) _ (by decide) _
  · have hq := hcomplete.2 (s + 1) (Nat.le_refl _)
    have e := walk_pass_all hq n (after.take n) (after.drop n) hn (by simp; omega)
    rw [List.take_append_drop] at e
    rw [e]
    exact ne_append (ne_fill false n (after.take n) (by simp; omega) _ (by decide))
      (by simp [fill_length]; omega) (ih _ _ _ _ hcomplete.1 (by simp; omega))

theorem walk_case15_ne {fuel : Nat} (ih : WalkNE fuel) {H kv after : List Byte} {s c k : Nat} (hH : HdrOK H s c)
    (hk : Varint kv k) (hk10 : kv.length ≤ 10) (hw : k % 8 = 1 ∨ k % 8 = 5) (hlen : (kv ++ after).length < fuel + 1) :
    NE (envWalk H s 0 (kv ++ after)) (fill .structure kv ++ envNext fuel k after) := by
  have hne := varint_ne_nil hk
  have hq : (envelopeScan (H ++ kv) s).1 = .pass (if k % 8 = 1 then 8 else 4) false :=
    query_ends hH (Nat.le_refl _) fun _ => envBody_fixed_pass hk hk10 hw (Nat.le_refl _) (drop_hdr H _)
  rw [walk_run_pass kv H after (by omega) (key_prefixes hH hk hk10) hq]
  have hcomplete := field_complete (s' := s + 1) (c' := c) hH (by omega) (by omega) (F := kv) fun p X kd hp =>
    ⟨kd, envBody_fixed hk hk10 hw (by omega) (drop_hdr H _)⟩
  refine ne_append (ne_fill true _ kv (Nat.le_refl _) _ (by decide)) (by simp [fill_length]) ?_
  rcases hw with hw | hw
  · have hn : envNext fuel k after = fill .envelope (after.take 8) ++ ReceiveSpec.envelope fuel (after.drop 8) := by
      unfold envNext; rw [hw]; rfl
    rw [hn]; simp only [hw, if_true]
    exact payload_tail_ne ih (by omega) hcomplete (by simp at hlen; omega)
  · have hn : envNext fuel k after = fill .envelope (after.take 4) ++ ReceiveSpec.envelope fuel (after.drop 4) := by
      unfold envNext; rw [hw]; rfl
    rw [hn]; simp only [hw, show (5 : Nat) ≠ 1 by decide, if_false]
    exact payload_tail_ne ih (by omega) hcomplete (by simp at hlen; omega)

theorem walk_case2_ne {fuel : Nat} (ih : WalkNE fuel) {H kv after : List Byte} {s c k : Nat} (hH : HdrOK H s c)
    (hk : Varint kv k) (hk10 : kv.length ≤ 10) (hw : k % 8 = 2) (hlen : (kv ++ after).length < fuel + 1) :
    NE (envWalk H s 0 (kv ++ after)) (fill .structure kv ++ envNext fuel k after) := by
  have hne := varint_ne_nil hk
  rw [walk_key hH hk hk10 (Or.inr hw)]
  have hn : envNext fuel k after = ReceiveSpec.delimitedThen false after (fill .envelope)
      (fun _ rest => ReceiveSpec.envelope fuel rest) := by
    unfold envNext; rw [hw]; rfl
  rw [hn]
  refine ne_append (ne_fill true _ kv (Nat.le_refl _) _ (by decide)) (by simp [fill_length]) ?_
  unfold ReceiveSpec.delimitedThen
  rcases varintEnd_cases 10 after with ⟨m2, he, h1, h2, h3, hv⟩ | ⟨he, hl, hu⟩ | ⟨he, hl, hu⟩
  · rw [varintThen_done he]
    generalize hrest : after.drop m2 = aft
    generalize hvv : after.take m2 = lv at hv
    have hafter : after = lv ++ aft := by rw [← hvv, ← hrest, List.take_append_drop]
    have hlv : lv.length = m2 := by rw [← hvv]; simp; omega
    have hl10 : lv.length ≤ 10 := by omega
    subst hafter
    simp only [Bool.false_eq_true, false_and, if_false]
    generalize hnv : varintValue lv = n at hv
    have hpre : ∀ j, 1 ≤ j → j < lv.length → ∃ b, (envelopeScan ((H ++ kv) ++ lv.take j) s).1 = .more b :=
      fun j _ hj => ⟨false, by
        rw [List.append_assoc]
        exact val_more hH hk hk10 (Or.inr hw) (varint_prefix hv j hj) (by simp; omega)⟩
    by_cases htw : k / 8 = 8 ∧ c ≠ 0
    · rw [walk_run_malformed lv (H ++ kv) aft (by omega) hpre (by
        rw [List.append_assoc]
        simpa using query_ends (T := kv ++ (lv ++ [])) hH (Nat.le_refl _) fun _ =>
          ends_twice hk hk10 hw hv hl10 htw.1 htw.2 (drop_hdr H _))]
      exact ne_rep true _ lv (Nat.le_refl _) _ (by decide) _
    · have round : ∀ (p : Nat) (X : List Byte) (kd : Nat), (n = 0 ∨ s < p) → ∃ kd',
          envBody (H ++ ((kv ++ lv) ++ X)) p ⟨none, c, kd, H.length, s⟩ =
            .yield ⟨none, if k / 8 = 8 then n else c, kd', H.length + (kv ++ lv).length,
              if n = 0 then s else s + 1⟩ := fun p X kd hp => ⟨kd, by
        rw [envBody_delim (B := H ++ ((kv ++ lv) ++ X)) (pos := H.length) (x := none) hk hk10 hw hv hl10 htw hp
          (by rw [drop_hdr, List.append_assoc]), List.length_append, Nat.add_assoc]⟩
      by_cases hn0 : n = 0
      · have hc := field_complete (s' := s) hH (Nat.le_refl _) (by simp; omega) (F := kv ++ lv)
          fun p X kd _ => by simpa [hn0] using round p X kd (Or.inl hn0)
        rw [walk_more lv (H ++ kv) aft (fun j h1 h2 => by
          by_cases hj : j < lv.length
          · exact hpre j h1 hj
          · refine ⟨true, ?_⟩
            rw [show j = lv.length by omega, List.take_length, List.append_assoc]
            exact hc.2 s (Nat.le_refl _))]
        refine ne_append (ne_fill true _ lv (Nat.le_refl _) _ (by decide)) (by simp [fill_length]) ?_
        simp only [hn0, List.take_zero, List.drop_zero, ReceiveSpec.fill, List.map_nil, List.nil_append]
        rw [List.append_assoc]
        exact ih aft _ s _ hc.1 (by simp at hlen; omega)
      · have hq : (envelopeScan ((H ++ kv) ++ lv) s).1 = .pass n (decide (k / 8 = 8)) := by
          rw [List.append_assoc]
          exact query_ends (T := kv ++ lv) hH (Nat.le_refl _) fun _ =>
            ends_delim_pass hk hk10 hw hv hl10 (by omega) (Nat.le_refl _) htw (drop_hdr H _)
        rw [walk_run_pass lv (H ++ kv) aft (by omega) hpre hq]
        refine ne_append (ne_fill true _ lv (Nat.le_refl _) _ (by decide)) (by simp [fill_length]) ?_
        have hc := field_complete (s' := s + 1) hH (by omega) (by simp; omega) (F := kv ++ lv)
          fun p X kd hp => by simpa [hn0] using round p X kd (Or.inr (by omega))
        rw [List.append_assoc]
        exact payload_tail_ne ih (by omega) hc (by simp at hlen; omega)
  · rw [varintThen_short he, valrun_short hH hk hk10 (Or.inr hw) hl hu]
    exact ne_fill true _ after (Nat.le_refl _) _ (by decide)
  · rw [varintThen_tooLong he, valrun_tooLong hH hk hk10 (Or.inr hw) hl hu]
    exact ne_rep true 10 (after.take 10) (by simp; omega) _ (by decide) _

theorem walk_caseBad_ne {fuel : Nat} {H kv after : List Byte} {s c k : Nat} (hH : HdrOK H s c)
    (hk : Varint kv k) (hk10 : kv.length ≤ 10) (hw : k % 8 ≠ 0 ∧ k % 8 ≠ 1 ∧ k % 8 ≠ 2 ∧ k % 8 ≠ 5) :
    NE (envWalk H s 0 (kv ++ after)) (fill .structure kv ++ envNext fuel k after) := by
  have hne := varint_ne_nil hk
  rw [walk_run_malformed kv H after (by omega) (key_prefixes hH hk hk10)
    (by simpa using query_ends (T := kv ++ []) hH (Nat.le_refl _) fun _ =>
      ends_bad_wire hk hk10 hw (drop_hdr H _))]
  exact ne_rep true _ kv (Nat.le_refl _) _ (by decide) _

/-- The walk covers no `error`, from every field boundary, on every byte string. -/
theorem envWalk_ne : ∀ fuel, WalkNE fuel
  | 0 => fun _ _ _ _ _ h => absurd h (Nat.not_lt_zero _)
  | fuel + 1 => fun E H s c hH hlen => by
    match E with
    | [] => simp only [envWalk]; exact ne_nil _
    | e :: es =>
      have ih := envWalk_ne fuel
      rw [envelope_cons]
      rcases varintEnd_cases 10 (e :: es) with ⟨m, he, h1, h2, h3, hk⟩ | ⟨he, hl, hu⟩ | ⟨he, hl, hu⟩
      · rw [varintThen_done he]
        generalize hafter : (e :: es).drop m = after
        generalize hkv : (e :: es).take m = kv at hk
        have hE : e :: es = kv ++ after := by rw [← hkv, ← hafter, List.take_append_drop]
        have hk10 : kv.length ≤ 10 := by rw [← hkv]; simp; omega
        rw [hE] at hlen ⊢
        generalize varintValue kv = k at hk
        unfold envNext
        by_cases w0 : k % 8 = 0
        · have := walk_case0_ne ih hH hk hk10 w0 hlen; unfold envNext at this; exact this
        by_cases w1 : k % 8 = 1
        · have := walk_case15_ne ih hH hk hk10 (Or.inl w1) hlen; unfold envNext at this; exact this
        by_cases w2 : k % 8 = 2
        · have := walk_case2_ne ih hH hk hk10 w2 hlen; unfold envNext at this; exact this
        by_cases w5 : k % 8 = 5
        · have := walk_case15_ne ih hH hk hk10 (Or.inr w5) hlen; unfold envNext at this; exact this
        · have := walk_caseBad_ne (fuel := fuel) (after := after) hH hk hk10 ⟨w0, w1, w2, w5⟩
          unfold envNext at this; exact this
      · rw [varintThen_short he]
        have := walk_more (s := s) (e :: es) H [] (fun j h1 h2 => ⟨false,
          query_ends hH (Nat.le_refl _) fun _ =>
            ends_key_unfinished (List.ne_nil_of_length_pos (by simp; omega)) (mem_take_of hu)
              (by simp; omega) (drop_hdr H _)⟩)
        rw [List.append_nil] at this
        rw [this]
        simpa [envWalk] using ne_fill true _ (e :: es) (Nat.le_refl _) Class.structure (by decide)
      · rw [varintThen_tooLong he]
        have ht : ((e :: es).take 10).length = 10 := by simp only [List.length_take]; omega
        have := walk_run_malformed (s := s) ((e :: es).take 10) H ((e :: es).drop 10) (by omega)
          (fun j h1 h2 => ⟨false,
            query_ends hH (Nat.le_refl _) fun _ =>
              ends_key_unfinished (List.ne_nil_of_length_pos (by simp; omega)) (mem_take_of hu)
                (by simp; omega) (drop_hdr H _)⟩)
          (query_ends hH (Nat.le_refl _) fun _ =>
            ends_key_tooLong (tooLong_of_drop (drop_hdr H _) (by omega) (mem_take_of hu)))
        rw [List.take_append_drop, ht] at this
        rw [this]
        exact ne_rep true 10 ((e :: es).take 10) (by rw [ht]; exact Nat.le_refl 10) _ (by decide) _

/-- **Every byte the walk of a delivered envelope covers, revealed or passed over, is not `error`**
(every byte string). -/
theorem envWalk_noErr (E : List Byte) :
    ∀ i, i < (envWalk [] 0 0 E).length → (ReceiveSpec.envelope (E.length + 1) E)[i]? ≠ some .error :=
  envWalk_ne (E.length + 1) E [] 0 0 hdrOK_nil (Nat.lt_succ_self _)

/-- The walk never ends on a byte string that goes on (it stops only after a refused byte). -/
theorem envWalk_ne_nil (h : List Byte) (p k : Nat) (b : Byte) (E : List Byte) : envWalk h p k (b :: E) ≠ [] := by
  cases k with
  | zero =>
    simp only [envWalk]
    split <;> simp
  | succ k =>
    simp only [envWalk]
    split
    · split <;> simp
    · simp

/-- **Item 3.** If the walk of a delivered envelope's bytes `E` went past all of them without being
refused (the walk of `E` followed by any byte is the walk of `E` and then the walk from some later
point), then no class of `E` is `error`: the hypothesis `NoErr` of `ReceiveRequestScan.qshape_skip`
for a `/api/v1/message` body. -/
theorem envelope_noErr (E : List Byte) (L : List Bool) (hd : List Byte) (p k : Nat)
    (hL : L.length = E.length) (hw : envWalk [] 0 0 (E ++ [0]) = L ++ envWalk hd p k [0]) :
    ∀ x ∈ ReceiveSpec.envelope (E.length + 1) E, x ≠ .error := by
  have hcov := envWalk_noErr (E ++ [0])
  rw [hw] at hcov
  have hlen : E.length < (L ++ envWalk hd p k [0]).length := by
    rw [List.length_append, hL]
    have : (envWalk hd p k [0]).length ≠ 0 := by
      intro e; exact envWalk_ne_nil hd p k 0 [] (List.eq_nil_of_length_eq_zero e)
    omega
  intro x hx hxe
  subst hxe
  obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hx
  have hil : i < E.length := by rw [ReceiveStream.envelope_len] at hi; exact hi
  have hF : (E ++ [0]).length + 1 = E.length + 2 := by simp
  rw [hF] at hcov
  have hpre := ReceiveStream.envelope_causal (E.length + 2) E [0] [] (fun e => by cases e)
  have hlenE : (ReceiveSpec.envelope (E.length + 2) E).length ≤ E.length := by
    rw [ReceiveStream.envelope_len]; exact Nat.le_refl _
  rw [List.append_nil, List.take_of_length_le hlenE,
    ReceiveStream.envelope_fuel (E.length + 2) (E.length + 1) E (by omega) (by omega)] at hpre
  have h1 := hcov i (by omega)
  apply h1
  have e2 : (ReceiveSpec.envelope (E.length + 2) (E ++ [0]))[i]? =
      ((ReceiveSpec.envelope (E.length + 2) (E ++ [0])).take E.length)[i]? := by
    rw [List.getElem?_take, if_pos hil]
  rw [e2, hpre, List.getElem?_eq_getElem hi, hix]

end ReceiveEnvDone
