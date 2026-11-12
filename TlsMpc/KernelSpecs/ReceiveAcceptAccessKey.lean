import TlsMpc.KernelSpecs.ReceiveAcceptText

/-!
# `receive-access-key`: the 72 layouts (T13, proof track P6)

New file; it changes no definition and no emitter imports it.

`receive-access-key` (`ReceiveFirst.withAccessKey`, proved equal to the kernel by
`ReceiveProofs.accessKey_spec`) finds the profile-key field after one of the 72 `gaps` (Signal-Android
writes `flags`, `expireTimer`, `expireTimerVersion` between the body and the profile key) and writes
the unidentified-access key derived from it into the conversation record. Its only opened output is
`status`.

PROVED here, for every one of the 72 layouts at once:
* `gap_unique`: two layouts never both match the same bytes (the claim in `ReceiveFirst.gaps`'s
  comment), by reading the fields in order: each starts with a distinct tag byte and each varint's
  width is fixed by its continuation bits (`varintShape_width_unique`);
* `withAccessKey_status`: the status is 255 exactly when some layout matches, 0 otherwise;
* `withAccessKey_accepted`: then the record holds AES-256 of `0^15 ‖ 02` under the 32 bytes after
  the matching layout's `32 20` (libsignal `ProfileKey::derive_access_key`: AES-256-GCM with a zero
  nonce over 16 zero bytes, whose first block is exactly that), everything else unchanged;
* `withAccessKey_rejected`: otherwise the record is unchanged.
-/
namespace TlsMpc.KernelSpecs.ReceiveAcceptAccessKey
open Std.Tactic.BVDecide
open TlsMpc TlsMpc.Signal
open Signal.ReceiveFirst
open ReceiveAccept
open ReceiveAcceptText (top_mk mk_true' mk_false')

/-! ### Varint widths -/

theorem varintShape_eq_255 (bytes : List (BitVec 8)) (off w : Nat) :
    varintShape ByteAuth.concrete bytes off w = 255 ↔
      (OpenResult.get ByteAuth.concrete bytes (off + w - 1)).toNat < 128 ∧
      ∀ j ∈ List.range (w - 1), 128 ≤ (OpenResult.get ByteAuth.concrete bytes (off + j)).toNat := by
  unfold varintShape
  rw [foldl_and_map_eq_255]
  simp only [top_mk, mk_not, mk_eq_255, Nat.not_le]

/-- The width of a varint is fixed by its continuation bits. -/
theorem varintShape_width_unique (bytes : List (BitVec 8)) (off w w' : Nat) (hw : 1 ≤ w) (hw' : 1 ≤ w')
    (h1 : varintShape ByteAuth.concrete bytes off w = 255) (h2 : varintShape ByteAuth.concrete bytes off w' = 255) :
    w = w' := by
  rw [varintShape_eq_255] at h1 h2
  rcases Nat.lt_trichotomy w w' with h | h | h
  · have a := h2.2 (w - 1) (List.mem_range.mpr (by omega))
    have b := h1.1
    rw [show off + w - 1 = off + (w - 1) by omega] at b
    omega
  · exact h
  · have a := h1.2 (w' - 1) (List.mem_range.mpr (by omega))
    have b := h2.1
    rw [show off + w' - 1 = off + (w' - 1) by omega] at b
    omega

/-! ### What a layout's mask says -/

theorem whenever_eq_255 (cond : Bool) (m : BitVec 8) :
    whenever ByteAuth.concrete cond m = 255 ↔ (cond = true → m = 255) := by
  cases cond
  · simp only [whenever, Bool.false_eq_true, if_false, false_imp_iff, iff_true]; rfl
  · simp [whenever]

theorem gapMask_eq_255 (c : List (BitVec 8)) (off : Nat) (g : Gap) :
    gapMask ByteAuth.concrete c off g = 255 ↔
      (g.flags ≠ 0 → OpenResult.get ByteAuth.concrete c off = ByteAuth.concrete.const 32 ∧
        varintShape ByteAuth.concrete c (off + 1) g.flags = 255) ∧
      (g.timer ≠ 0 →
        OpenResult.get ByteAuth.concrete c (off + (if g.flags = 0 then 0 else 1 + g.flags)) = ByteAuth.concrete.const 40 ∧
        varintShape ByteAuth.concrete c (off + (if g.flags = 0 then 0 else 1 + g.flags) + 1) g.timer = 255) ∧
      (g.version ≠ 0 →
        OpenResult.get ByteAuth.concrete c (off + (if g.flags = 0 then 0 else 1 + g.flags) +
          (if g.timer = 0 then 0 else 1 + g.timer)) = ByteAuth.concrete.const 184 ∧
        OpenResult.get ByteAuth.concrete c (off + (if g.flags = 0 then 0 else 1 + g.flags) +
          (if g.timer = 0 then 0 else 1 + g.timer) + 1) = ByteAuth.concrete.const 1 ∧
        varintShape ByteAuth.concrete c (off + (if g.flags = 0 then 0 else 1 + g.flags) +
          (if g.timer = 0 then 0 else 1 + g.timer) + 2) g.version = 255) ∧
      OpenResult.get ByteAuth.concrete c (off + g.size) = ByteAuth.concrete.const 50 ∧
      OpenResult.get ByteAuth.concrete c (off + g.size + 1) = ByteAuth.concrete.const 32 := by
  unfold gapMask
  simp only [all_eq_255, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true,
    whenever_eq_255, concrete_and, and_eq_255, eqMask_eq_255, bne_iff_ne, ne_eq]

/-- **Two layouts never both match** (at the same offset in the same content). -/
theorem gap_unique (c : List (BitVec 8)) (off : Nat) (g g' : Gap)
    (h : gapMask ByteAuth.concrete c off g = 255) (h' : gapMask ByteAuth.concrete c off g' = 255) : g = g' := by
  obtain ⟨f, t, v⟩ := g
  obtain ⟨f', t', v'⟩ := g'
  rw [gapMask_eq_255] at h h'
  simp only [Gap.size] at h h'
  obtain ⟨hf, ht, hv, hk, -⟩ := h
  obtain ⟨hf', ht', hv', hk', -⟩ := h'
  rw [← Nat.add_assoc, ← Nat.add_assoc] at hk hk'
  have c32_40 : ByteAuth.concrete.const 32 ≠ ByteAuth.concrete.const 40 := by decide
  have c32_184 : ByteAuth.concrete.const 32 ≠ ByteAuth.concrete.const 184 := by decide
  have c32_50 : ByteAuth.concrete.const 32 ≠ ByteAuth.concrete.const 50 := by decide
  have c40_184 : ByteAuth.concrete.const 40 ≠ ByteAuth.concrete.const 184 := by decide
  have c40_50 : ByteAuth.concrete.const 40 ≠ ByteAuth.concrete.const 50 := by decide
  have c184_50 : ByteAuth.concrete.const 184 ≠ ByteAuth.concrete.const 50 := by decide
  -- flags
  have ef : f = f' := by
    by_cases a : f = 0 <;> by_cases b : f' = 0
    · omega
    · exfalso
      have h32 := (hf' b).1
      simp only [a, if_true, Nat.add_zero] at ht hv hk
      by_cases ta : t = 0
      · by_cases va : v = 0
        · simp only [ta, va, if_true, Nat.add_zero] at hk
          exact c32_50 (h32.symm.trans hk)
        · simp only [ta, if_true, Nat.add_zero] at hv
          exact c32_184 (h32.symm.trans (hv va).1)
      · exact c32_40 (h32.symm.trans (ht ta).1)
    · exfalso
      have h32 := (hf a).1
      simp only [b, if_true, Nat.add_zero] at ht' hv' hk'
      by_cases ta : t' = 0
      · by_cases va : v' = 0
        · simp only [ta, va, if_true, Nat.add_zero] at hk'
          exact c32_50 (h32.symm.trans hk')
        · simp only [ta, if_true, Nat.add_zero] at hv'
          exact c32_184 (h32.symm.trans (hv' va).1)
      · exact c32_40 (h32.symm.trans (ht' ta).1)
    · exact varintShape_width_unique c (off + 1) f f' (by omega) (by omega) (hf a).2 (hf' b).2
  subst ef
  generalize off + (if f = 0 then 0 else 1 + f) = T at ht ht' hv hv' hk hk'
  -- timer
  have et : t = t' := by
    by_cases a : t = 0 <;> by_cases b : t' = 0
    · omega
    · exfalso
      have h40 := (ht' b).1
      simp only [a, if_true, Nat.add_zero] at hv hk
      by_cases va : v = 0
      · simp only [va, if_true, Nat.add_zero] at hk
        exact c40_50 (h40.symm.trans hk)
      · exact c40_184 (h40.symm.trans (hv va).1)
    · exfalso
      have h40 := (ht a).1
      simp only [b, if_true, Nat.add_zero] at hv' hk'
      by_cases va : v' = 0
      · simp only [va, if_true, Nat.add_zero] at hk'
        exact c40_50 (h40.symm.trans hk')
      · exact c40_184 (h40.symm.trans (hv' va).1)
    · exact varintShape_width_unique c (T + 1) t t' (by omega) (by omega) (ht a).2 (ht' b).2
  subst et
  generalize T + (if t = 0 then 0 else 1 + t) = V at hv hv' hk hk'
  -- version
  have ev : v = v' := by
    by_cases a : v = 0 <;> by_cases b : v' = 0
    · omega
    · exfalso
      simp only [a, if_true, Nat.add_zero] at hk
      exact c184_50 ((hv' b).1.symm.trans hk)
    · exfalso
      simp only [b, if_true, Nat.add_zero] at hk'
      exact c184_50 ((hv a).1.symm.trans hk')
    · exact varintShape_width_unique c (V + 2) v v' (by omega) (by omega) (hv a).2.2 (hv' b).2.2
  subst ev
  rfl

/-! ### The status and the record -/

instance : DecidableEq Gap := fun a b =>
  if h : a.flags = b.flags ∧ a.timer = b.timer ∧ a.version = b.version then
    isTrue (by cases a; cases b; simp only at h; obtain ⟨rfl, rfl, rfl⟩ := h; rfl)
  else isFalse (by intro e; subst e; exact h ⟨rfl, rfl, rfl⟩)

theorem gaps_length : gaps.length = 72 := by decide

theorem gaps_nodup : gaps.Nodup := by decide

theorem isMask_gapMask (c : List (BitVec 8)) (off : Nat) (g : Gap) : IsMask (gapMask ByteAuth.concrete c off g) := by
  unfold gapMask
  apply isMask_all
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  refine ⟨isMask_whenever _ (isMask_and (isMask_eqMask _ _) (isMask_varintShape _ _ _)),
    isMask_whenever _ (isMask_and (isMask_eqMask _ _) (isMask_varintShape _ _ _)),
    isMask_whenever _ (isMask_all _ ?_), isMask_eqMask _ _, isMask_eqMask _ _⟩
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  exact ⟨isMask_eqMask _ _, isMask_eqMask _ _, isMask_varintShape _ _ _⟩

theorem keyChoices_eq (c : List (BitVec 8)) (off j : Nat) (gs : List Gap) :
    keyChoices ByteAuth.concrete c off j gs (gs.map (gapMask ByteAuth.concrete c off)) =
      gs.map (fun g => (gapMask ByteAuth.concrete c off g, OpenResult.get ByteAuth.concrete c (off + g.size + 2 + j))) := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp only [List.map_cons, keyChoices, ih]

theorem pick_zero (ps : List (BitVec 8 × BitVec 8)) (hz : ∀ p ∈ ps, p.1 = 0) (acc : BitVec 8) :
    ps.foldl (fun acc choice => ByteAuth.concrete.xor acc (ByteAuth.concrete.and choice.1 choice.2)) acc = acc := by
  induction ps generalizing acc with
  | nil => rfl
  | cons p ps ih =>
      rw [List.foldl_cons, hz p (by simp), concrete_and, concrete_xor, zero_and', xor_zero']
      exact ih (fun q hq => hz q (by simp [hq])) acc

theorem pick_unique {α : Type} (gs : List α) (hnd : gs.Nodup) (F : α → BitVec 8 × BitVec 8) (g0 : α) (hg0 : g0 ∈ gs)
    (h0 : (F g0).1 = 255) (hz : ∀ g ∈ gs, g ≠ g0 → (F g).1 = 0) (acc : BitVec 8) :
    (gs.map F).foldl (fun acc choice => ByteAuth.concrete.xor acc (ByteAuth.concrete.and choice.1 choice.2)) acc =
      acc ^^^ (F g0).2 := by
  induction gs generalizing acc with
  | nil => simp at hg0
  | cons g gs ih =>
      rw [List.map_cons, List.foldl_cons]
      have hnd' := List.nodup_cons.mp hnd
      by_cases e : g = g0
      · subst e
        rw [h0, concrete_and, concrete_xor, ones_and']
        apply pick_zero
        intro p hp
        obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hp
        exact hz g' (by simp [hg']) (fun h => hnd'.1 (h ▸ hg'))
      · rw [hz g (by simp) e, concrete_and, concrete_xor, zero_and', xor_zero']
        have hg0' : g0 ∈ gs := by
          rcases List.mem_cons.mp hg0 with h | h
          · exact absurd h.symm e
          · exact h
        exact ih hnd'.2 hg0' (fun g' hg' => hz g' (by simp [hg'])) acc

theorem foldl_either_zeros (ms : List (BitVec 8)) (hz : ∀ m ∈ ms, m = 0) (acc : BitVec 8) :
    ms.foldl (either ByteAuth.concrete) acc = acc := by
  induction ms generalizing acc with
  | nil => rfl
  | cons m ms ih =>
      rw [List.foldl_cons, hz m (by simp), either_concrete, or_zero']
      exact ih (fun q hq => hz q (by simp [hq])) acc

/-- Some layout matches. -/
def Found (c : List (BitVec 8)) (off : Nat) : Prop := ∃ g ∈ gaps, gapMask ByteAuth.concrete c off g = 255

instance (c : List (BitVec 8)) (off : Nat) : Decidable (Found c off) := inferInstanceAs (Decidable (∃ g ∈ gaps, _))

theorem any_gaps (c : List (BitVec 8)) (off : Nat) :
    any ByteAuth.concrete (gaps.map (gapMask ByteAuth.concrete c off)) = mk (Found c off) := by
  by_cases hex : Found c off
  · obtain ⟨g, hg, hm⟩ := hex
    rw [mk_true' _ ⟨g, hg, hm⟩, any]
    exact foldl_either_255 _ _ (Or.inr (List.mem_map.mpr ⟨g, hg, hm⟩))
  · rw [mk_false' _ hex, any]
    apply foldl_either_zeros
    intro m hm
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hm
    rcases isMask_gapMask c off g with h | h
    · exact h
    · exact absurd ⟨g, hg, h⟩ hex

/-- The 32 bytes after the matching layout's `32 20`. -/
def profileKey (c : List (BitVec 8)) (off : Nat) (g : Gap) : List (BitVec 8) :=
  (List.range 32).map (fun j => OpenResult.get ByteAuth.concrete c (off + g.size + 2 + j))

/-- AES-256 of the block `0^15 ‖ 02` under `key`: libsignal `ProfileKey::derive_access_key`
(AES-256-GCM, zero nonce, 16 zero bytes: the ciphertext is the keystream block for counter 2). -/
def accessKeyOf (key : List (BitVec 8)) : List (BitVec 8) :=
  Aes.encryptExpanded Aes.concrete 14 (Aes.expandKey Aes.concrete 8 14 key)
    (lit ByteAuth.concrete (List.replicate 15 0 ++ [2]))

/-- **`receive-access-key`'s status is 255 exactly when one of the 72 layouts matches** (and 0
otherwise). -/
theorem withAccessKey_status (cert offset : Nat) (conversation plain : List (BitVec 8)) :
    (withAccessKey Aes.concrete ByteAuth.concrete cert offset conversation plain).getD 0 [] =
      [mk (Found (plain.drop 8) offset)] := by
  simp only [withAccessKey, List.getD_cons_zero, any_gaps]

/-- **When a layout `g` matches**, the record is the input record with bytes `cert + 278 ..
cert + 294` (the access key in the metadata) replaced by the access key derived from the 32 bytes
after `g`'s `32 20`. -/
theorem withAccessKey_accepted (cert offset : Nat) (conversation plain : List (BitVec 8))
    (hlen : cert + 294 ≤ conversation.length) (g : Gap) (hg : g ∈ gaps)
    (hm : gapMask ByteAuth.concrete (plain.drop 8) offset g = 255) :
    withAccessKey Aes.concrete ByteAuth.concrete cert offset conversation plain =
      [[255], conversation.take (cert + 278) ++ accessKeyOf (profileKey (plain.drop 8) offset g) ++
        conversation.drop (cert + 294)] := by
  simp only [withAccessKey]
  rw [any_gaps, mk_true' _ ⟨g, hg, hm⟩]
  have hkey : (List.range 32).map (fun j => pick ByteAuth.concrete (keyChoices ByteAuth.concrete (plain.drop 8) offset j
      gaps (gaps.map (gapMask ByteAuth.concrete (plain.drop 8) offset)))) = profileKey (plain.drop 8) offset g := by
    apply List.map_congr_left
    intro j _
    rw [pick, keyChoices_eq, pick_unique gaps gaps_nodup _ g hg hm]
    · exact zero_xor' _
    · intro g' hg' hne
      rcases isMask_gapMask (plain.drop 8) offset g' with h | h
      · exact h
      · exact absurd (gap_unique _ _ g' g h hm) hne
  rw [hkey, ChainSend.selectState_accept]
  · rfl
  · rw [Aes.encryptExpanded_length _ _ _ _ (Aes.expandKey_length _ _ _ _ (by simp [profileKey]) (by decide))]
    simp [Establish.part]
    omega

/-- **When no layout matches**, the record is unchanged. -/
theorem withAccessKey_rejected (cert offset : Nat) (conversation plain : List (BitVec 8))
    (hno : ¬Found (plain.drop 8) offset) :
    withAccessKey Aes.concrete ByteAuth.concrete cert offset conversation plain = [[0], conversation] := by
  simp only [withAccessKey]
  rw [any_gaps, mk_false' _ hno, ChainSend.selectState_reject]
  congr 2
  simp only [Establish.part, List.append_assoc]
  rw [show conversation.drop (cert + 294) = (conversation.drop (cert + 278)).drop 16 by
    rw [List.drop_drop]]
  rw [List.take_append_drop, List.take_append_drop]

end TlsMpc.KernelSpecs.ReceiveAcceptAccessKey
