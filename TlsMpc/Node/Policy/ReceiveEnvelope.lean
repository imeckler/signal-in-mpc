import TlsMpc.Node.Policy.ReceiveProofs

/-!
# T1 inside a delivered envelope (proof track P1)

REORGANIZATION_PLAN.md section 8, T1. New file; it changes no definition. No emitter or executable
imports it.

Inside a delivered envelope (`State.inner`) the controller reveals one byte at a time and decides
after each whether the next bytes are a field's payload, to be passed over (`envelopeAdvance`,
`envelopeScan` on the envelope's revealed bytes). `envWalk` is that walk over an envelope's bytes;
`envelope_payload_unrevealed` says it reveals no byte the reference (`ReceiveSpec.envelope`) calls
a payload, for every byte string (standard axioms only).

How: `envelopeScan`'s loop is rewritten as `loopG envBody` (`envelopeScan_eq`, by `rfl`); `HdrOK`
says the revealed bytes so far are complete fields, which the loop walks to their end
(`hdrOK_extend`); the round lemmas (`envBody_*`, `ends_*`) give the scanner's answer after them;
the reference is split by its own varint reader (`varintEnd_cases`): a complete key, an unfinished
one, a too-long one; then by wire type (`walk_case0`, `walk_case15`, `walk_case2`, `walk_caseBad`),
each field's bytes revealed or passed exactly as the reference classes them, and induction on the
rest (`envWalk_safe`).

Not covered here: that the controller's `step`/`stepSkipped` follow `envWalk` (their envelope part
is `envelopeAdvance` on `State.inner`; `envWalk` leaves out the checks against the body's length,
which only refuse, so the controller reveals a prefix of what `envWalk` reveals).
-/

namespace ReceiveProofs

open PublicReceive

/-! ### `envelopeScan`'s loop as a function -/

/-- The loop's state: the early answer, then `content`, `kind`, `pos`, `seen`. -/
abbrev EnvState := MProd (Option (EnvelopeNeed × Nat × Nat)) (MProd Nat (MProd Nat (MProd Nat Nat)))

/-- After a fixed-width or length-delimited field's count is known (`c`: the content length kept). -/
def envField (bytes : List Byte) (p key count after c : Nat) (r : EnvState) : ForInStep EnvState :=
  if (count == 0) = true then .yield ⟨none, c, r.snd.snd.fst, after, r.snd.snd.snd.snd⟩
  else if r.snd.snd.snd.snd < p then .yield ⟨none, c, r.snd.snd.fst, after, r.snd.snd.snd.snd + 1⟩
  else if (after == bytes.length) = true then
    .done ⟨some (.pass count (key % 8 == 2 && key / 8 == 8), r.snd.snd.fst, c), c, r.snd.snd.fst,
      r.snd.snd.snd.fst, r.snd.snd.snd.snd⟩
  else .done ⟨some (.malformed, r.snd.snd.fst, c), c, r.snd.snd.fst, r.snd.snd.snd.fst, r.snd.snd.snd.snd⟩

def envCount (bytes : List Byte) (p key count after : Nat) (r : EnvState) : ForInStep EnvState :=
  if (key % 8 == 2 && key / 8 == 8) = true then
    if (r.snd.fst != 0) = true then
      .done ⟨some (.malformed, r.snd.snd.fst, r.snd.fst), r.snd.fst, r.snd.snd.fst, r.snd.snd.snd.fst,
        r.snd.snd.snd.snd⟩
    else envField bytes p key count after count r
  else envField bytes p key count after r.snd.fst r

/-- The answer when no complete varint is at `at`. -/
def envUnfinished (bytes : List Byte) (at_ : Nat) (r : EnvState) : ForInStep EnvState :=
  .done ⟨some (if varintTooLong bytes at_ = true then .malformed else .more false, r.snd.snd.fst, r.snd.fst),
    r.snd.fst, r.snd.snd.fst, r.snd.snd.snd.fst, r.snd.snd.snd.snd⟩

/-- One round of `envelopeScan`'s loop. -/
def envBody (bytes : List Byte) (p : Nat) (r : EnvState) : ForInStep EnvState :=
  if r.snd.snd.snd.fst ≥ bytes.length then
    .done ⟨some (.more true, r.snd.snd.fst, r.snd.fst), r.snd.fst, r.snd.snd.fst, r.snd.snd.snd.fst,
      r.snd.snd.snd.snd⟩
  else
  match varintAt bytes r.snd.snd.snd.fst with
  | some (key, next) =>
    if (key % 8 == 0) = true then
      match varintAt bytes next with
      | some (value, after) =>
        if (key / 8 == 1) = true then .yield ⟨none, r.snd.fst, value, after, r.snd.snd.snd.snd⟩
        else .yield ⟨none, r.snd.fst, r.snd.snd.fst, after, r.snd.snd.snd.snd⟩
      | _ => envUnfinished bytes next r
    else if (key % 8 == 1 || key % 8 == 2 || key % 8 == 5) = true then
      if (key % 8 == 2) = true then
        match varintAt bytes next with
        | some found => envCount bytes p key found.fst found.snd r
        | none => envUnfinished bytes next r
      else envCount bytes p key (if (key % 8 == 1) = true then 8 else 4) next r
    else .done ⟨some (.malformed, r.snd.snd.fst, r.snd.fst), r.snd.fst, r.snd.snd.fst, r.snd.snd.snd.fst,
      r.snd.snd.snd.snd⟩
  | _ => envUnfinished bytes r.snd.snd.snd.fst r

def envResult (r : EnvState) : EnvelopeNeed × Nat × Nat :=
  match r.fst with
  | none => (.more false, r.snd.snd.fst, r.snd.fst)
  | some a => a

theorem envelopeScan_eq (bytes : List Byte) (p : Nat) :
    envelopeScan bytes p = envResult (loopG (envBody bytes p) (bytes.length + 1) ⟨none, 0, 0, 0, 0⟩) := by
  unfold envelopeScan
  simp only [Id.run, forIn_range]
  rw [forIn_ignore (envBody bytes p) _ _ ?hf, List.length_range']
  · unfold envResult
    generalize loopG (envBody bytes p) (bytes.length + 1) ⟨none, 0, 0, 0, 0⟩ = r
    obtain ⟨fst, snd⟩ := r
    cases fst <;> rfl
  · intro x r; rfl

/-! ### The reference's varints -/

open ReceiveSpec (fill varintEnd varintValue varintThen VarintEnd)

theorem varintEnd_varint : ∀ {v : List Byte} {n : Nat}, Varint v n → ∀ (a : Nat) (rest : List Byte),
    v.length ≤ a → varintEnd a (v ++ rest) = .done v.length
  | _, _, .last hb, a + 1, rest, _ => by simp [varintEnd, hb]
  | _, _, .last _, 0, _, h => by simp at h
  | _, _, .cont (b := b) (rest := r) hb hr, a + 1, rest, h => by
    have := varintEnd_varint hr a rest (by simp at h; omega)
    simp only [List.cons_append, varintEnd, this, List.length_cons]
    rw [if_neg (by omega)]
  | _, _, .cont _ _, 0, _, h => by simp at h

theorem varintValue_varint : ∀ {v : List Byte} {n : Nat}, Varint v n → varintValue v = n
  | _, _, .last hb => by simp [varintValue, Nat.mod_eq_of_lt hb]
  | _, _, .cont _ hr => by simp [varintValue, varintValue_varint hr]

/-- What `varintEnd` says, as facts: a complete varint, an unfinished one, or a too-long one. -/
theorem varintEnd_cases : ∀ (a : Nat) (E : List Byte),
    (∃ m, varintEnd a E = .done m ∧ 1 ≤ m ∧ m ≤ a ∧ m ≤ E.length ∧ Varint (E.take m) (varintValue (E.take m))) ∨
    (varintEnd a E = .short ∧ E.length < a ∧ ∀ y ∈ E, 128 ≤ y.toNat) ∨
    (varintEnd a E = .tooLong ∧ a ≤ E.length ∧ ∀ y ∈ E.take a, 128 ≤ y.toNat)
  | 0, E => Or.inr (Or.inr ⟨rfl, by omega, by simp⟩)
  | a + 1, [] => Or.inr (Or.inl ⟨rfl, by simp, by simp⟩)
  | a + 1, b :: rest => by
    by_cases hb : b.toNat < 128
    · refine Or.inl ⟨1, by simp [varintEnd, hb], Nat.le_refl _, by omega, by simp, ?_⟩
      have : varintValue [b] = b.toNat := by simp [varintValue, Nat.mod_eq_of_lt hb]
      simpa [this] using Varint.last hb
    · have hb' : 128 ≤ b.toNat := by omega
      rcases varintEnd_cases a rest with ⟨m, he, h1, h2, h3, hv⟩ | ⟨he, hl, hu⟩ | ⟨he, hl, hu⟩
      · refine Or.inl ⟨m + 1, by simp [varintEnd, hb, he], by omega, by omega, by simp; omega, ?_⟩
        simp only [List.take_succ_cons, varintValue]
        exact Varint.cont hb' hv
      · refine Or.inr (Or.inl ⟨by simp [varintEnd, hb, he], by simp; omega, ?_⟩)
        intro y hy; simp at hy; rcases hy with rfl | hy; exact hb'; exact hu y hy
      · refine Or.inr (Or.inr ⟨by simp [varintEnd, hb, he], by simp; omega, ?_⟩)
        intro y hy; simp only [List.take_succ_cons, List.mem_cons] at hy
        rcases hy with rfl | hy; exact hb'; exact hu y hy

/-! ### Revealed flags against classes -/

/-- Every revealed position (`true`) has a public class. -/
abbrev SafeFor (R : List Bool) (C : List ReceiveSpec.Class) : Prop :=
  ∀ i : Nat, R[i]? = some true → ∃ c : ReceiveSpec.Class, C[i]? = some c ∧ c.secret = false

theorem safeFor_nil (C : List ReceiveSpec.Class) : SafeFor [] C := by
  intro i h; simp at h

theorem safeFor_append {R1 R2 : List Bool} {C1 C2 : List ReceiveSpec.Class} (h1 : SafeFor R1 C1)
    (hl : R1.length = C1.length) (h2 : SafeFor R2 C2) : SafeFor (R1 ++ R2) (C1 ++ C2) := by
  intro i hi
  by_cases hlt : i < R1.length
  · rw [List.getElem?_append_left hlt] at hi
    obtain ⟨c, hc, hs⟩ := h1 i hi
    exact ⟨c, by rw [List.getElem?_append_left (by omega)]; exact hc, hs⟩
  · rw [List.getElem?_append_right (by omega)] at hi
    obtain ⟨c, hc, hs⟩ := h2 _ hi
    exact ⟨c, by rw [List.getElem?_append_right (by omega), ← hl]; exact hc, hs⟩

theorem safeFor_true {α : Type} (T : List α) (c : ReceiveSpec.Class) (hc : c.secret = false) (C : List ReceiveSpec.Class) :
    SafeFor (List.replicate T.length true) (fill c T ++ C) := by
  intro i hi
  have : i < T.length := by
    rcases Nat.lt_or_ge i T.length with h | h
    · exact h
    · rw [List.getElem?_eq_none (by simp; omega)] at hi; cases hi
  exact ⟨c, by rw [List.getElem?_append_left (by simp [fill]; omega)]; simp [fill, this], hc⟩

theorem safeFor_false (n : Nat) (C : List ReceiveSpec.Class) : SafeFor (List.replicate n false) C := by
  intro i hi
  rw [List.getElem?_replicate] at hi
  split at hi <;> simp at hi

theorem safeFor_true_prefix {α : Type} (T : List α) (k : Nat) (hk : k ≤ T.length) (c : ReceiveSpec.Class)
    (hc : c.secret = false) (C : List ReceiveSpec.Class) :
    SafeFor (List.replicate k true) (fill c T ++ C) := by
  intro i hi
  have : i < k := by
    rcases Nat.lt_or_ge i k with h | h
    · exact h
    · rw [List.getElem?_eq_none (by simp; omega)] at hi; cases hi
  refine ⟨c, ?_, hc⟩
  rw [List.getElem?_append_left (by simp [fill]; omega)]
  simp [fill, show i < T.length by omega]

/-! ### The loop, round by round -/

/-- `n` rounds of a loop, all continuing, take `b` to `b'`. -/
def Reaches {β : Type} (g : β → ForInStep β) : Nat → β → β → Prop
  | 0, b, b' => b = b'
  | n + 1, b, b' => ∃ b1, g b = .yield b1 ∧ Reaches g n b1 b'

theorem loopG_reaches {β : Type} {g : β → ForInStep β} : ∀ (n m : Nat) (b b' : β), Reaches g n b b' →
    loopG g (n + m) b = loopG g m b'
  | 0, m, b, b', h => by cases h; simp
  | n + 1, m, b, b', ⟨b1, h1, h2⟩ => by
    rw [show n + 1 + m = (n + m) + 1 by omega, loopG_yield _ h1]
    exact loopG_reaches n m b1 b' h2

theorem reaches_snoc {β : Type} {g : β → ForInStep β} : ∀ (n : Nat) (b b1 b2 : β), Reaches g n b b1 →
    g b1 = .yield b2 → Reaches g (n + 1) b b2
  | 0, b, b1, b2, h, h1 => by cases h; exact ⟨b2, h1, rfl⟩
  | n + 1, b, b1, b2, ⟨c, hc, h⟩, h1 => ⟨c, hc, reaches_snoc n c b1 b2 h h1⟩

/-- The facts a round needs about a key at `pos`. -/
theorem key_at {B kv rest : List Byte} {pos k : Nat} (hk : Varint kv k) (hk10 : kv.length ≤ 10)
    (h : B.drop pos = kv ++ rest) :
    varintAt B pos = some (k, pos + kv.length) ∧ ¬ B.length ≤ pos ∧ B.drop (pos + kv.length) = rest ∧
      B.length = pos + kv.length + rest.length := by
  have hne := varint_ne_nil hk
  have hlen := length_of_drop h (List.ne_nil_of_length_pos (by simp; omega))
  simp only [List.length_append] at hlen
  exact ⟨varintAt_varint hk hk10 h, by omega, drop_after h, by omega⟩

/-- A complete varint field (wire type 0): the loop goes on after it. -/
theorem envBody_varint {B kv vv rest : List Byte} {p pos k v c kd seen : Nat} {x : Option (EnvelopeNeed × Nat × Nat)}
    (hk : Varint kv k) (hk10 : kv.length ≤ 10) (hw : k % 8 = 0) (hv : Varint vv v) (hv10 : vv.length ≤ 10)
    (h : B.drop pos = kv ++ (vv ++ rest)) :
    ∃ kd', envBody B p ⟨x, c, kd, pos, seen⟩ = .yield ⟨none, c, kd', pos + kv.length + vv.length, seen⟩ := by
  obtain ⟨h1, hp, hd, -⟩ := key_at hk hk10 h
  have h2 := varintAt_varint hv hv10 hd
  unfold envBody
  simp only [ge_iff_le, hp, if_false, h1, h2, hw, beq_self_eq_true, if_true]
  split
  · exact ⟨v, rfl⟩
  · exact ⟨kd, rfl⟩

/-- A fixed-width field (wire type 1 or 5) whose payload was passed: the loop goes on after it. -/
theorem envBody_fixed {B kv rest : List Byte} {p pos k c kd seen : Nat} {x : Option (EnvelopeNeed × Nat × Nat)}
    (hk : Varint kv k) (hk10 : kv.length ≤ 10) (hw : k % 8 = 1 ∨ k % 8 = 5) (hs : seen < p)
    (h : B.drop pos = kv ++ rest) :
    envBody B p ⟨x, c, kd, pos, seen⟩ = .yield ⟨none, c, kd, pos + kv.length, seen + 1⟩ := by
  obtain ⟨h1, hp, -, -⟩ := key_at hk hk10 h
  unfold envBody envCount envField
  rcases hw with hw | hw <;>
    simp [hp, h1, hw, hs]

/-- A fixed-width field's key at the end of the revealed bytes, its payload not passed: pass it. -/
theorem envBody_fixed_pass {B kv : List Byte} {p pos k c kd seen : Nat} {x : Option (EnvelopeNeed × Nat × Nat)}
    (hk : Varint kv k) (hk10 : kv.length ≤ 10) (hw : k % 8 = 1 ∨ k % 8 = 5) (hs : p ≤ seen)
    (h : B.drop pos = kv) :
    ∃ r, envBody B p ⟨x, c, kd, pos, seen⟩ = .done r ∧
      (envResult r).1 = .pass (if k % 8 = 1 then 8 else 4) false := by
  obtain ⟨h1, hp, -, hl⟩ := key_at (rest := []) hk hk10 (by simpa using h)
  unfold envBody envCount envField
  have hne := varint_ne_nil hk
  rcases hw with hw | hw <;>
    simp [h1, hw, show ¬ seen < p by omega, hl, envResult, show ¬ pos + kv.length ≤ pos by omega]

/-- A length-delimited field whose payload (if any) was passed: the loop goes on after it, unless
it is a second content field. -/
theorem envBody_delim {B kv lv rest : List Byte} {p pos k n c kd seen : Nat} {x : Option (EnvelopeNeed × Nat × Nat)}
    (hk : Varint kv k) (hk10 : kv.length ≤ 10) (hw : k % 8 = 2) (hl : Varint lv n) (hl10 : lv.length ≤ 10)
    (hc : ¬ (k / 8 = 8 ∧ c ≠ 0)) (hs : n = 0 ∨ seen < p) (h : B.drop pos = kv ++ (lv ++ rest)) :
    envBody B p ⟨x, c, kd, pos, seen⟩ = .yield ⟨none, if k / 8 = 8 then n else c, kd,
      pos + kv.length + lv.length, if n = 0 then seen else seen + 1⟩ := by
  obtain ⟨h1, hp, hd, -⟩ := key_at hk hk10 h
  have h2 := varintAt_varint hl hl10 hd
  unfold envBody envCount envField
  by_cases h8 : k / 8 = 8
  · have hc0 : c = 0 := by omega
    rcases hs with hs | hs
    · subst hs; simp [hp, h1, h2, hw, h8, hc0]
    · by_cases hn : n = 0
      · subst hn; simp [hp, h1, h2, hw, h8, hc0]
      · simp [hp, h1, h2, hw, h8, hc0, hn, hs]
  · rcases hs with hs | hs
    · subst hs; simp [hp, h1, h2, hw, h8]
    · by_cases hn : n = 0
      · subst hn; simp [hp, h1, h2, hw, h8]
      · simp [hp, h1, h2, hw, h8, hn, hs]

/-! Rounds that end the loop, and the answer they give. -/

/-- The loop's answer: `envelopeScan`'s first component. -/
def Ends (s : ForInStep EnvState) (need : EnvelopeNeed) : Prop := ∃ r, s = .done r ∧ (envResult r).1 = need

theorem ends_end {B : List Byte} {p pos c kd seen : Nat} {x : Option (EnvelopeNeed × Nat × Nat)}
    (h : B.length ≤ pos) : Ends (envBody B p ⟨x, c, kd, pos, seen⟩) (.more true) := by
  unfold envBody; simp [h, Ends, envResult]

theorem ends_key_unfinished {B u : List Byte} {p pos c kd seen : Nat} {x : Option (EnvelopeNeed × Nat × Nat)}
    (hne : u ≠ []) (hu : ∀ y ∈ u, 128 ≤ y.toNat) (hl : u.length < 10) (h : B.drop pos = u) :
    Ends (envBody B p ⟨x, c, kd, pos, seen⟩) (.more false) := by
  have hlen := length_of_drop h hne
  have hpos : 0 < u.length := by
    cases u with
    | nil => exact absurd rfl hne
    | cons _ _ => simp
  unfold envBody envUnfinished
  simp [Ends, envResult, show ¬ B.length ≤ pos by omega, varintAt_partial hu h, varintTooLong_short h hl]

theorem ends_key_tooLong {B : List Byte} {p pos c kd seen : Nat} {x : Option (EnvelopeNeed × Nat × Nat)}
    (h : varintTooLong B pos = true) : Ends (envBody B p ⟨x, c, kd, pos, seen⟩) .malformed := by
  have := tooLong_length h
  unfold envBody envUnfinished
  simp [Ends, envResult, show ¬ B.length ≤ pos by omega, varintAt_tooLong h, h]

theorem ends_value_unfinished {B kv u : List Byte} {p pos k c kd seen : Nat} {x : Option (EnvelopeNeed × Nat × Nat)}
    (hk : Varint kv k) (hk10 : kv.length ≤ 10) (hw : k % 8 = 0 ∨ k % 8 = 2) (hu : ∀ y ∈ u, 128 ≤ y.toNat)
    (hl : u.length < 10) (h : B.drop pos = kv ++ u) :
    Ends (envBody B p ⟨x, c, kd, pos, seen⟩) (.more false) := by
  obtain ⟨h1, hp, hd, -⟩ := key_at hk hk10 h
  unfold envBody envUnfinished
  rcases hw with hw | hw <;>
    simp [Ends, envResult, hp, h1, hw, varintAt_partial hu hd, varintTooLong_short hd hl]

theorem ends_value_tooLong {B kv rest : List Byte} {p pos k c kd seen : Nat} {x : Option (EnvelopeNeed × Nat × Nat)}
    (hk : Varint kv k) (hk10 : kv.length ≤ 10) (hw : k % 8 = 0 ∨ k % 8 = 2)
    (h : B.drop pos = kv ++ rest) (ht : varintTooLong B (pos + kv.length) = true) :
    Ends (envBody B p ⟨x, c, kd, pos, seen⟩) .malformed := by
  obtain ⟨h1, hp, -, -⟩ := key_at hk hk10 h
  unfold envBody envUnfinished
  rcases hw with hw | hw <;>
    simp [Ends, envResult, hp, h1, hw, varintAt_tooLong ht, ht]

theorem ends_bad_wire {B kv rest : List Byte} {p pos k c kd seen : Nat} {x : Option (EnvelopeNeed × Nat × Nat)}
    (hk : Varint kv k) (hk10 : kv.length ≤ 10) (hw : k % 8 ≠ 0 ∧ k % 8 ≠ 1 ∧ k % 8 ≠ 2 ∧ k % 8 ≠ 5)
    (h : B.drop pos = kv ++ rest) : Ends (envBody B p ⟨x, c, kd, pos, seen⟩) .malformed := by
  obtain ⟨h1, hp, -, -⟩ := key_at hk hk10 h
  obtain ⟨a, b, d, e⟩ := hw
  unfold envBody
  simp [Ends, envResult, hp, h1, a, b, d, e]

theorem ends_twice {B kv lv rest : List Byte} {p pos k n c kd seen : Nat} {x : Option (EnvelopeNeed × Nat × Nat)}
    (hk : Varint kv k) (hk10 : kv.length ≤ 10) (hw : k % 8 = 2) (hl : Varint lv n) (hl10 : lv.length ≤ 10)
    (h8 : k / 8 = 8) (hc : c ≠ 0) (h : B.drop pos = kv ++ (lv ++ rest)) :
    Ends (envBody B p ⟨x, c, kd, pos, seen⟩) .malformed := by
  obtain ⟨h1, hp, hd, -⟩ := key_at hk hk10 h
  have h2 := varintAt_varint hl hl10 hd
  unfold envBody envCount
  simp [Ends, envResult, hp, h1, h2, hw, h8, hc]

theorem ends_delim_pass {B kv lv : List Byte} {p pos k n c kd seen : Nat} {x : Option (EnvelopeNeed × Nat × Nat)}
    (hk : Varint kv k) (hk10 : kv.length ≤ 10) (hw : k % 8 = 2) (hl : Varint lv n) (hl10 : lv.length ≤ 10)
    (hn : 0 < n) (hs : p ≤ seen) (hc : ¬ (k / 8 = 8 ∧ c ≠ 0)) (h : B.drop pos = kv ++ lv) :
    Ends (envBody B p ⟨x, c, kd, pos, seen⟩) (.pass n (decide (k / 8 = 8))) := by
  obtain ⟨h1, hp, hd, hlen⟩ := key_at (rest := lv) hk hk10 h
  have h2 := varintAt_varint (rest := []) hl hl10 (by simpa using hd)
  have hn0 : n ≠ 0 := by omega
  have hne := varint_ne_nil hk
  have hq : ¬ pos + kv.length + lv.length ≤ pos := by omega
  unfold envBody envCount envField
  by_cases h8 : k / 8 = 8
  · have hc0 : c = 0 := by omega
    simp [Ends, envResult, h1, h2, hw, h8, hc0, hn0, show ¬ seen < p by omega, hlen, hq]
  · simp [Ends, envResult, h1, h2, hw, h8, hn0, show ¬ seen < p by omega, hlen, hq]

/-! ### Complete fields, and the scanner's answer after them -/

/-- `H` is an envelope's revealed bytes made of complete fields: whatever follows and whatever
`passed ≥ s`, the loop walks `H` and stops at its end with `s` payloads seen and content length
`c`. -/
def HdrOK (H : List Byte) (s c : Nat) : Prop :=
  ∀ (p : Nat) (X : List Byte), s ≤ p → ∃ m kd, m ≤ H.length ∧
    Reaches (envBody (H ++ X) p) m ⟨none, 0, 0, 0, 0⟩ ⟨none, c, kd, H.length, s⟩

theorem hdrOK_nil : HdrOK [] 0 0 := fun _ _ _ => ⟨0, 0, Nat.le_refl _, rfl⟩

theorem hdrOK_extend {H F : List Byte} {s c s' c' : Nat} (hH : HdrOK H s c) (hs : s ≤ s') (hF : 0 < F.length)
    (hstep : ∀ (p : Nat) (X : List Byte) (kd : Nat), s' ≤ p → ∃ kd',
      envBody (H ++ (F ++ X)) p ⟨none, c, kd, H.length, s⟩ = .yield ⟨none, c', kd', H.length + F.length, s'⟩) :
    HdrOK (H ++ F) s' c' := by
  intro p X hp
  obtain ⟨m, kd, hm, hr⟩ := hH p (F ++ X) (by omega)
  obtain ⟨kd', hy⟩ := hstep p X kd hp
  refine ⟨m + 1, kd', by simp; omega, ?_⟩
  rw [List.append_assoc, List.length_append]
  exact reaches_snoc m _ _ _ hr hy

/-- The scanner's answer when the round after `H`'s complete fields ends the loop. -/
theorem query_ends {H T : List Byte} {s c p : Nat} {need : EnvelopeNeed} (hH : HdrOK H s c) (hp : s ≤ p)
    (hend : ∀ kd, Ends (envBody (H ++ T) p ⟨none, c, kd, H.length, s⟩) need) :
    (envelopeScan (H ++ T) p).1 = need := by
  obtain ⟨m, kd, hm, hr⟩ := hH p T hp
  obtain ⟨r, hr1, hr2⟩ := hend kd
  rw [envelopeScan_eq, show (H ++ T).length + 1 = m + ((H ++ T).length - m + 1) by simp; omega,
    loopG_reaches _ _ _ _ hr, loopG_done _ hr1]
  exact hr2

/-- The scanner's answer when the round after `H` completes a field that ends the bytes: more. -/
theorem query_yield_end {H T : List Byte} {s c p : Nat} (hH : HdrOK H s c) (hp : s ≤ p) (hT : 0 < T.length)
    (hstep : ∀ kd, ∃ c' kd' s', envBody (H ++ T) p ⟨none, c, kd, H.length, s⟩ =
      .yield ⟨none, c', kd', (H ++ T).length, s'⟩) :
    (envelopeScan (H ++ T) p).1 = .more true := by
  obtain ⟨m, kd, hm, hr⟩ := hH p T hp
  obtain ⟨c', kd', s', hy⟩ := hstep kd
  obtain ⟨r, hr1, hr2⟩ := ends_end (B := H ++ T) (p := p) (pos := (H ++ T).length) (c := c') (kd := kd')
    (seen := s') (x := none) (Nat.le_refl _)
  rw [envelopeScan_eq, show (H ++ T).length + 1 = m + (((H ++ T).length - m - 1) + 1 + 1) by simp; omega,
    loopG_reaches _ _ _ _ hr, loopG_yield _ hy, loopG_done _ hr1]
  exact hr2

/-! ### The walk -/

/-- The controller's walk of a delivered envelope's bytes (`envelopeAdvance` on each revealed byte,
`stepSkipped` on each passed one; the checks against the body's length, which only refuse more,
left out): for each byte, revealed (`true`) or passed (`false`), until a refused byte (revealed,
then nothing). -/
def envWalk : List Byte → Nat → Nat → List Byte → List Bool
  | _, _, _, [] => []
  | header, passed, skip + 1, _ :: rest =>
    if skip = 0 then
      match (envelopeScan header (passed + 1)).1 with
      | .pass count _ => false :: envWalk header (passed + 1) count rest
      | .more _ => false :: envWalk header (passed + 1) 0 rest
      | .malformed => [false]
    else false :: envWalk header passed skip rest
  | header, passed, 0, b :: rest =>
    match (envelopeScan (header ++ [b]) passed).1 with
    | .malformed => [true]
    | .more _ => true :: envWalk (header ++ [b]) passed 0 rest
    | .pass count _ => true :: envWalk (header ++ [b]) passed count rest

/-- A run of revealed bytes on which the scanner asks for more. -/
theorem walk_more {s : Nat} : ∀ (T H E' : List Byte),
    (∀ j, 1 ≤ j → j ≤ T.length → ∃ b, (envelopeScan (H ++ T.take j) s).1 = .more b) →
    envWalk H s 0 (T ++ E') = List.replicate T.length true ++ envWalk (H ++ T) s 0 E'
  | [], H, E', _ => by simp
  | t :: T, H, E', h => by
    obtain ⟨b, hb⟩ := h 1 (by omega) (by simp)
    simp only [List.take_succ_cons, List.take_zero] at hb
    simp only [List.cons_append, envWalk, hb, List.length_cons, List.replicate_succ, List.cons_append]
    rw [walk_more T (H ++ [t]) E' (fun j h1 h2 => by
      obtain ⟨b', hb'⟩ := h (j + 1) (by omega) (by simp; omega)
      exact ⟨b', by simpa [List.take_succ_cons] using hb'⟩)]
    simp

theorem walk_malformed {s : Nat} {H : List Byte} {b : Byte} {E' : List Byte}
    (h : (envelopeScan (H ++ [b]) s).1 = .malformed) : envWalk H s 0 (b :: E') = [true] := by
  simp [envWalk, h]

theorem walk_pass {s n : Nat} {H : List Byte} {b : Byte} {E' : List Byte} {f : Bool}
    (h : (envelopeScan (H ++ [b]) s).1 = .pass n f) : envWalk H s 0 (b :: E') = true :: envWalk (H ++ [b]) s n E' := by
  simp [envWalk, h]

/-- A payload running past the bytes: all passed. -/
theorem walk_pass_short {s : Nat} {H : List Byte} : ∀ (n : Nat) (E : List Byte), 0 < n → E.length < n →
    envWalk H s n E = List.replicate E.length false
  | _, [], _, _ => rfl
  | n + 1, e :: E, _, hl => by
    simp only [List.length_cons] at hl
    have hn : n ≠ 0 := by omega
    simp only [envWalk, hn, if_false, List.length_cons, List.replicate_succ]
    rw [walk_pass_short n E (by omega) (by omega)]

/-- A whole payload passed, then the walk resumes at a field boundary. -/
theorem walk_pass_all {s : Nat} {H : List Byte} {b : Bool} (hq : (envelopeScan H (s + 1)).1 = .more b) :
    ∀ (n : Nat) (P E' : List Byte), 0 < n → P.length = n →
      envWalk H s n (P ++ E') = List.replicate n false ++ envWalk H (s + 1) 0 E'
  | _, [], _, h0, hl => by simp at hl; omega
  | n + 1, e :: P, E', _, hl => by
    simp only [List.length_cons] at hl
    by_cases hn : n = 0
    · subst hn
      have : P = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      simp [envWalk, hq]
    · simp only [List.cons_append, envWalk, hn, if_false, List.replicate_succ, List.cons_append]
      rw [walk_pass_all hq n P E' (by omega) (by omega)]

/-! ### The reference, one field at a time -/

/-- What `ReceiveSpec.envelope` does after a key. -/
def envNext (fuel key : Nat) (after : List Byte) : List ReceiveSpec.Class :=
  match key % 8 with
  | 0 => varintThen after fun _ rest => ReceiveSpec.envelope fuel rest
  | 1 => fill .envelope (after.take 8) ++ ReceiveSpec.envelope fuel (after.drop 8)
  | 5 => fill .envelope (after.take 4) ++ ReceiveSpec.envelope fuel (after.drop 4)
  | 2 => ReceiveSpec.delimitedThen false after (fill .envelope) fun _ rest => ReceiveSpec.envelope fuel rest
  | _ => fill .error after

theorem envelope_cons (fuel : Nat) (e : Byte) (es : List Byte) :
    ReceiveSpec.envelope (fuel + 1) (e :: es) = varintThen (e :: es) (envNext fuel) := rfl

theorem varintThen_done {E : List Byte} {m : Nat} {next : Nat → List Byte → List ReceiveSpec.Class}
    (h : varintEnd 10 E = .done m) :
    varintThen E next = fill .structure (E.take m) ++ next (varintValue (E.take m)) (E.drop m) := by
  unfold varintThen; rw [h]

theorem varintThen_short {E : List Byte} {next : Nat → List Byte → List ReceiveSpec.Class}
    (h : varintEnd 10 E = .short) : varintThen E next = fill .structure E := by
  unfold varintThen; rw [h]

theorem varintThen_tooLong {E : List Byte} {next : Nat → List Byte → List ReceiveSpec.Class}
    (h : varintEnd 10 E = .tooLong) :
    varintThen E next = fill .structure (E.take 10) ++ fill .error (E.drop 10) := by
  unfold varintThen; rw [h]

theorem tooLong_of_drop {B u : List Byte} {pos : Nat} (h : B.drop pos = u) (hl : 10 ≤ u.length)
    (hu : ∀ y ∈ u.take 10, 128 ≤ y.toNat) : varintTooLong B pos = true := by
  unfold varintTooLong
  rw [List.all_eq_true]
  intro i hi
  have hi' := List.mem_range.mp hi
  have hlen := congrArg List.length h
  rw [List.length_drop] at hlen
  have hget : PublicReceive.get B (pos + i) = u[i]'(by omega) := by
    unfold PublicReceive.get
    rw [List.getD_eq_getElem?_getD, ← List.getElem?_drop, h, List.getElem?_eq_getElem (by omega)]
    rfl
  have := hu (u[i]'(by omega)) (List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩)
  simp only [Bool.and_eq_true, decide_eq_true_eq, hget]
  exact ⟨by omega, this⟩

/-! ### The scanner's answers inside one field -/

theorem drop_hdr (H T : List Byte) : (H ++ T).drop H.length = T := List.drop_left

theorem key_prefix_more {H kv : List Byte} {s c k : Nat} (hH : HdrOK H s c) (hk : Varint kv k)
    (hk10 : kv.length ≤ 10) (j : Nat) (hj1 : 1 ≤ j) (hj : j < kv.length) :
    (envelopeScan (H ++ kv.take j) s).1 = .more false :=
  query_ends hH (Nat.le_refl _) fun _ =>
    ends_key_unfinished (List.ne_nil_of_length_pos (by simp; omega)) (varint_prefix hk j hj)
      (by simp; omega) (drop_hdr H _)

theorem val_more {H kv u : List Byte} {s c k : Nat} (hH : HdrOK H s c) (hk : Varint kv k)
    (hk10 : kv.length ≤ 10) (hw : k % 8 = 0 ∨ k % 8 = 2) (hu : ∀ y ∈ u, 128 ≤ y.toNat) (hl : u.length < 10) :
    (envelopeScan (H ++ (kv ++ u)) s).1 = .more false :=
  query_ends hH (Nat.le_refl _) fun _ => ends_value_unfinished hk hk10 hw hu hl (drop_hdr H _)

/-- Revealing a key of wire type 0 or 2: the scanner asks for more at each byte. -/
theorem walk_key {H kv E' : List Byte} {s c k : Nat} (hH : HdrOK H s c) (hk : Varint kv k)
    (hk10 : kv.length ≤ 10) (hw : k % 8 = 0 ∨ k % 8 = 2) :
    envWalk H s 0 (kv ++ E') = List.replicate kv.length true ++ envWalk (H ++ kv) s 0 E' := by
  apply walk_more
  intro j h1 h2
  by_cases hj : j < kv.length
  · exact ⟨false, key_prefix_more hH hk hk10 j h1 hj⟩
  · rw [show j = kv.length by omega, List.take_length]
    exact ⟨false, by simpa using val_more (u := []) hH hk hk10 hw (by simp) (by simp)⟩

theorem walk_more1 {s : Nat} {H : List Byte} {b : Byte} {rest : List Byte} {x : Bool}
    (h : (envelopeScan (H ++ [b]) s).1 = .more x) : envWalk H s 0 (b :: rest) = true :: envWalk (H ++ [b]) s 0 rest := by
  simp only [envWalk, h]

/-- A run of revealed bytes whose last byte is refused. -/
theorem walk_run_malformed {s : Nat} : ∀ (T H E' : List Byte), 0 < T.length →
    (∀ j, 1 ≤ j → j < T.length → ∃ b, (envelopeScan (H ++ T.take j) s).1 = .more b) →
    (envelopeScan (H ++ T) s).1 = .malformed →
    envWalk H s 0 (T ++ E') = List.replicate T.length true
  | [], _, _, h, _, _ => by simp at h
  | [t], H, E', _, _, hm => by simpa using walk_malformed (E' := E') hm
  | t :: t' :: T, H, E', _, h, hm => by
    obtain ⟨b, hb⟩ := h 1 (by omega) (by simp)
    simp only [List.take_succ_cons, List.take_zero] at hb
    have := walk_run_malformed (t' :: T) (H ++ [t]) E' (by simp) (fun j h1 h2 => by
      obtain ⟨b', hb'⟩ := h (j + 1) (by omega) (by simp at h2 ⊢; omega)
      exact ⟨b', by simpa [List.take_succ_cons] using hb'⟩) (by simpa using hm)
    rw [List.cons_append] at this
    rw [List.cons_append, walk_more1 hb, List.cons_append, this]
    simp [List.replicate_succ]

/-- A run of revealed bytes whose last byte starts a payload of `n` bytes. -/
theorem walk_run_pass {s n : Nat} {f : Bool} : ∀ (T H E' : List Byte), 0 < T.length →
    (∀ j, 1 ≤ j → j < T.length → ∃ b, (envelopeScan (H ++ T.take j) s).1 = .more b) →
    (envelopeScan (H ++ T) s).1 = .pass n f →
    envWalk H s 0 (T ++ E') = List.replicate T.length true ++ envWalk (H ++ T) s n E'
  | [], _, _, h, _, _ => by simp at h
  | [t], H, E', _, _, hm => by simpa using walk_pass (E' := E') hm
  | t :: t' :: T, H, E', _, h, hm => by
    obtain ⟨b, hb⟩ := h 1 (by omega) (by simp)
    simp only [List.take_succ_cons, List.take_zero] at hb
    have := walk_run_pass (t' :: T) (H ++ [t]) E' (by simp) (fun j h1 h2 => by
      obtain ⟨b', hb'⟩ := h (j + 1) (by omega) (by simp at h2 ⊢; omega)
      exact ⟨b', by simpa [List.take_succ_cons] using hb'⟩) (by simpa using hm)
    rw [List.cons_append] at this
    rw [List.cons_append, walk_more1 hb, List.cons_append, this]
    simp [List.replicate_succ]

theorem key_prefixes {H kv : List Byte} {s c k : Nat} (hH : HdrOK H s c) (hk : Varint kv k) (hk10 : kv.length ≤ 10) :
    ∀ j, 1 ≤ j → j < kv.length → ∃ b, (envelopeScan (H ++ kv.take j) s).1 = .more b :=
  fun j h1 h2 => ⟨false, key_prefix_more hH hk hk10 j h1 h2⟩

theorem safeFor_fill {α : Type} (T : List α) (c : ReceiveSpec.Class) (hc : c.secret = false) :
    SafeFor (List.replicate T.length true) (fill c T) := by
  simpa using safeFor_true T c hc []

theorem fill_length {α : Type} (c : ReceiveSpec.Class) (T : List α) : (fill c T).length = T.length := by
  simp [fill]

/-- The induction hypothesis: the walk is safe from any field boundary, on bytes shorter than `fuel`. -/
def WalkSafe (fuel : Nat) : Prop := ∀ (E H : List Byte) (s c : Nat), HdrOK H s c → E.length < fuel →
  SafeFor (envWalk H s 0 E) (ReceiveSpec.envelope fuel E)

theorem mem_take_of {u : List Byte} {j : Nat} (hu : ∀ y ∈ u, 128 ≤ y.toNat) : ∀ y ∈ u.take j, 128 ≤ y.toNat :=
  fun y hy => hu y (List.mem_of_mem_take hy)

/-- A value or length the bytes end inside: all of it revealed. -/
theorem valrun_short {H kv after : List Byte} {s c k : Nat} (hH : HdrOK H s c) (hk : Varint kv k)
    (hk10 : kv.length ≤ 10) (hw : k % 8 = 0 ∨ k % 8 = 2) (hl : after.length < 10) (hu : ∀ y ∈ after, 128 ≤ y.toNat) :
    envWalk (H ++ kv) s 0 after = List.replicate after.length true := by
  have := walk_more (s := s) after (H ++ kv) [] (fun j h1 h2 => ⟨false, by
    rw [List.append_assoc]
    exact val_more hH hk hk10 hw (mem_take_of hu) (by simp; omega)⟩)
  simpa [envWalk] using this

/-- A value or length of more than 10 bytes: refused at its 10th. -/
theorem valrun_tooLong {H kv after : List Byte} {s c k : Nat} (hH : HdrOK H s c) (hk : Varint kv k)
    (hk10 : kv.length ≤ 10) (hw : k % 8 = 0 ∨ k % 8 = 2) (hl : 10 ≤ after.length)
    (hu : ∀ y ∈ after.take 10, 128 ≤ y.toNat) :
    envWalk (H ++ kv) s 0 after = List.replicate 10 true := by
  have ht : (after.take 10).length = 10 := by simp; omega
  have := walk_run_malformed (s := s) (after.take 10) (H ++ kv) (after.drop 10) (by omega)
    (fun j h1 h2 => ⟨false, by
      rw [List.append_assoc]
      exact val_more hH hk hk10 hw (mem_take_of hu) (by simp; omega)⟩)
    (by
      rw [List.append_assoc]
      exact query_ends hH (Nat.le_refl _) fun _ =>
        ends_value_tooLong hk hk10 hw (drop_hdr H _)
          (tooLong_of_drop (by rw [← List.drop_drop, drop_hdr, drop_hdr]) (by omega)
            (mem_take_of hu)))
  rw [List.take_append_drop, ht] at this
  exact this

/-- A field completed in one round: the bytes after it are a new field boundary, and when they
end, the scanner asks for more. -/
theorem field_complete {H F : List Byte} {s c s' c' : Nat} (hH : HdrOK H s c) (hs : s ≤ s') (hF : 0 < F.length)
    (round : ∀ (p : Nat) (X : List Byte) (kd : Nat), s' ≤ p → ∃ kd',
      envBody (H ++ (F ++ X)) p ⟨none, c, kd, H.length, s⟩ = .yield ⟨none, c', kd', H.length + F.length, s'⟩) :
    HdrOK (H ++ F) s' c' ∧ ∀ p, s' ≤ p → (envelopeScan (H ++ F) p).1 = .more true := by
  refine ⟨hdrOK_extend hH hs hF round, fun p hp => query_yield_end hH (by omega) hF fun kd => ?_⟩
  obtain ⟨kd', e⟩ := round p [] kd hp
  exact ⟨c', kd', s', by simpa using e⟩

theorem round_varint {H kv vv : List Byte} {s c k v : Nat} (hk : Varint kv k) (hk10 : kv.length ≤ 10)
    (hw : k % 8 = 0) (hv : Varint vv v) (hv10 : vv.length ≤ 10) :
    ∀ (p : Nat) (X : List Byte) (kd : Nat), s ≤ p → ∃ kd',
      envBody (H ++ ((kv ++ vv) ++ X)) p ⟨none, c, kd, H.length, s⟩ =
        .yield ⟨none, c, kd', H.length + (kv ++ vv).length, s⟩ := by
  intro p X kd _
  obtain ⟨kd', e⟩ := envBody_varint (B := H ++ ((kv ++ vv) ++ X)) (p := p) (x := none) (c := c) (kd := kd)
    (seen := s) hk hk10 hw hv hv10 (by rw [drop_hdr, List.append_assoc])
  exact ⟨kd', by rw [e, List.length_append, Nat.add_assoc]⟩

/-- After a key of wire type 0: its value, then the next fields. -/
theorem value_tail {fuel : Nat} (ih : WalkSafe fuel) {H kv after : List Byte} {s c k : Nat} (hH : HdrOK H s c)
    (hk : Varint kv k) (hk10 : kv.length ≤ 10) (hw : k % 8 = 0 ∨ k % 8 = 2)
    (hlen : kv.length + after.length < fuel + 1)
    (hcomplete : ∀ vv v, Varint vv v → vv.length ≤ 10 →
      HdrOK (H ++ (kv ++ vv)) s c ∧ ∀ p, s ≤ p → (envelopeScan (H ++ (kv ++ vv)) p).1 = .more true) :
    SafeFor (envWalk (H ++ kv) s 0 after) (varintThen after fun _ rest => ReceiveSpec.envelope fuel rest) := by
  have hne := varint_ne_nil hk
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
    refine safeFor_append (safeFor_fill vv _ rfl) (by simp [fill_length]) ?_
    rw [List.append_assoc]
    exact ih _ _ s c hH' (by simp at hlen; omega)
  · rw [varintThen_short he, valrun_short hH hk hk10 hw hl hu]
    exact safeFor_fill after _ rfl
  · rw [varintThen_tooLong he, valrun_tooLong hH hk hk10 hw hl hu]
    have := safeFor_true (after.take 10) ReceiveSpec.Class.structure rfl (fill ReceiveSpec.Class.error (after.drop 10))
    rwa [show (after.take 10).length = 10 by simp; omega] at this

/-- **Wire type 0**: a varint value; nothing is passed, everything revealed is structure. -/
theorem walk_case0 {fuel : Nat} (ih : WalkSafe fuel) {H kv after : List Byte} {s c k : Nat} (hH : HdrOK H s c)
    (hk : Varint kv k) (hk10 : kv.length ≤ 10) (hw : k % 8 = 0) (hlen : (kv ++ after).length < fuel + 1) :
    SafeFor (envWalk H s 0 (kv ++ after)) (fill .structure kv ++ envNext fuel k after) := by
  have hne := varint_ne_nil hk
  rw [walk_key hH hk hk10 (Or.inl hw)]
  have hn : envNext fuel k after = varintThen after (fun _ rest => ReceiveSpec.envelope fuel rest) := by
    unfold envNext; rw [hw]; rfl
  rw [hn]
  refine safeFor_append (safeFor_fill kv _ rfl) (by simp [fill_length]) ?_
  exact value_tail ih hH hk hk10 (Or.inl hw) (by simpa using hlen)
    (fun vv v hv hv10 => field_complete hH (Nat.le_refl s) (by simp; have := varint_ne_nil hv; omega)
      (round_varint (H := H) hk hk10 hw hv hv10))

/-- A payload of `n > 0` bytes after a field's structure `F`: all passed, then the next fields. -/
theorem payload_tail {fuel : Nat} (ih : WalkSafe fuel) {H F after : List Byte} {s c' n : Nat} (hn : 0 < n)
    (hcomplete : HdrOK (H ++ F) (s + 1) c' ∧ ∀ p, s + 1 ≤ p → (envelopeScan (H ++ F) p).1 = .more true)
    (hlen : after.length < fuel + n) :
    SafeFor (envWalk (H ++ F) s n after)
      (fill ReceiveSpec.Class.envelope (after.take n) ++ ReceiveSpec.envelope fuel (after.drop n)) := by
  by_cases hs : after.length < n
  · rw [walk_pass_short n after hn hs]; exact safeFor_false _ _
  · have hq := hcomplete.2 (s + 1) (Nat.le_refl _)
    have e := walk_pass_all hq n (after.take n) (after.drop n) hn (by simp; omega)
    rw [List.take_append_drop] at e
    rw [e]
    exact safeFor_append (safeFor_false n _) (by simp [fill_length]; omega)
      (ih _ _ _ _ hcomplete.1 (by simp; omega))

/-- **Wire types 1 and 5**: the key revealed, the 8 or 4 bytes after it passed. -/
theorem walk_case15 {fuel : Nat} (ih : WalkSafe fuel) {H kv after : List Byte} {s c k : Nat} (hH : HdrOK H s c)
    (hk : Varint kv k) (hk10 : kv.length ≤ 10) (hw : k % 8 = 1 ∨ k % 8 = 5) (hlen : (kv ++ after).length < fuel + 1) :
    SafeFor (envWalk H s 0 (kv ++ after)) (fill .structure kv ++ envNext fuel k after) := by
  have hne := varint_ne_nil hk
  have hq : (envelopeScan (H ++ kv) s).1 = .pass (if k % 8 = 1 then 8 else 4) false :=
    query_ends hH (Nat.le_refl _) fun _ => envBody_fixed_pass hk hk10 hw (Nat.le_refl _) (drop_hdr H _)
  rw [walk_run_pass kv H after (by omega) (key_prefixes hH hk hk10) hq]
  have hcomplete := field_complete (s' := s + 1) (c' := c) hH (by omega) (by omega) (F := kv) fun p X kd hp =>
    ⟨kd, envBody_fixed hk hk10 hw (by omega) (drop_hdr H _)⟩
  refine safeFor_append (safeFor_fill kv _ rfl) (by simp [fill_length]) ?_
  rcases hw with hw | hw
  · have hn : envNext fuel k after = fill .envelope (after.take 8) ++ ReceiveSpec.envelope fuel (after.drop 8) := by
      unfold envNext; rw [hw]; rfl
    rw [hn]; simp only [hw, if_true]
    exact payload_tail ih (by omega) hcomplete (by simp at hlen; omega)
  · have hn : envNext fuel k after = fill .envelope (after.take 4) ++ ReceiveSpec.envelope fuel (after.drop 4) := by
      unfold envNext; rw [hw]; rfl
    rw [hn]; simp only [hw, show (5 : Nat) ≠ 1 by decide, if_false]
    exact payload_tail ih (by omega) hcomplete (by simp at hlen; omega)

/-- **Wire type 2**: the key and the length revealed, the payload passed (a second content field
refused at its length). -/
theorem walk_case2 {fuel : Nat} (ih : WalkSafe fuel) {H kv after : List Byte} {s c k : Nat} (hH : HdrOK H s c)
    (hk : Varint kv k) (hk10 : kv.length ≤ 10) (hw : k % 8 = 2) (hlen : (kv ++ after).length < fuel + 1) :
    SafeFor (envWalk H s 0 (kv ++ after)) (fill .structure kv ++ envNext fuel k after) := by
  have hne := varint_ne_nil hk
  rw [walk_key hH hk hk10 (Or.inr hw)]
  have hn : envNext fuel k after = ReceiveSpec.delimitedThen false after (fill .envelope)
      (fun _ rest => ReceiveSpec.envelope fuel rest) := by
    unfold envNext; rw [hw]; rfl
  rw [hn]
  refine safeFor_append (safeFor_fill kv _ rfl) (by simp [fill_length]) ?_
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
      exact safeFor_true lv _ rfl _
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
        refine safeFor_append (safeFor_fill lv _ rfl) (by simp [fill_length]) ?_
        simp only [hn0, List.take_zero, List.drop_zero, ReceiveSpec.fill, List.map_nil, List.nil_append]
        rw [List.append_assoc]
        exact ih aft _ s _ hc.1 (by simp at hlen; omega)
      · have hq : (envelopeScan ((H ++ kv) ++ lv) s).1 = .pass n (decide (k / 8 = 8)) := by
          rw [List.append_assoc]
          exact query_ends (T := kv ++ lv) hH (Nat.le_refl _) fun _ =>
            ends_delim_pass hk hk10 hw hv hl10 (by omega) (Nat.le_refl _) htw (drop_hdr H _)
        rw [walk_run_pass lv (H ++ kv) aft (by omega) hpre hq]
        refine safeFor_append (safeFor_fill lv _ rfl) (by simp [fill_length]) ?_
        have hc := field_complete (s' := s + 1) hH (by omega) (by simp; omega) (F := kv ++ lv)
          fun p X kd hp => by simpa [hn0] using round p X kd (Or.inr (by omega))
        rw [List.append_assoc]
        exact payload_tail ih (by omega) hc (by simp at hlen; omega)
  · rw [varintThen_short he, valrun_short hH hk hk10 (Or.inr hw) hl hu]
    exact safeFor_fill after _ rfl
  · rw [varintThen_tooLong he, valrun_tooLong hH hk hk10 (Or.inr hw) hl hu]
    have := safeFor_true (after.take 10) ReceiveSpec.Class.structure rfl (fill ReceiveSpec.Class.error (after.drop 10))
    rwa [show (after.take 10).length = 10 by simp; omega] at this

/-- **Other wire types**: the key revealed, then refused. -/
theorem walk_caseBad {fuel : Nat} {H kv after : List Byte} {s c k : Nat} (hH : HdrOK H s c)
    (hk : Varint kv k) (hk10 : kv.length ≤ 10) (hw : k % 8 ≠ 0 ∧ k % 8 ≠ 1 ∧ k % 8 ≠ 2 ∧ k % 8 ≠ 5) :
    SafeFor (envWalk H s 0 (kv ++ after)) (fill .structure kv ++ envNext fuel k after) := by
  have hne := varint_ne_nil hk
  rw [walk_run_malformed kv H after (by omega) (key_prefixes hH hk hk10)
    (by simpa using query_ends (T := kv ++ []) hH (Nat.le_refl _) fun _ =>
      ends_bad_wire hk hk10 hw (drop_hdr H _))]
  exact safeFor_true kv _ rfl _

/-- The walk is safe from every field boundary, on every byte string. -/
theorem envWalk_safe : ∀ fuel, WalkSafe fuel
  | 0 => fun _ _ _ _ _ h => absurd h (Nat.not_lt_zero _)
  | fuel + 1 => fun E H s c hH hlen => by
    match E with
    | [] => simp only [envWalk]; exact safeFor_nil _
    | e :: es =>
      have ih := envWalk_safe fuel
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
        · have := walk_case0 ih hH hk hk10 w0 hlen; unfold envNext at this; exact this
        by_cases w1 : k % 8 = 1
        · have := walk_case15 ih hH hk hk10 (Or.inl w1) hlen; unfold envNext at this; exact this
        by_cases w2 : k % 8 = 2
        · have := walk_case2 ih hH hk hk10 w2 hlen; unfold envNext at this; exact this
        by_cases w5 : k % 8 = 5
        · have := walk_case15 ih hH hk hk10 (Or.inr w5) hlen; unfold envNext at this; exact this
        · have := walk_caseBad (fuel := fuel) (after := after) hH hk hk10 ⟨w0, w1, w2, w5⟩
          unfold envNext at this; exact this
      · rw [varintThen_short he]
        have := walk_more (s := s) (e :: es) H [] (fun j h1 h2 => ⟨false,
          query_ends hH (Nat.le_refl _) fun _ =>
            ends_key_unfinished (List.ne_nil_of_length_pos (by simp; omega)) (mem_take_of hu)
              (by simp; omega) (drop_hdr H _)⟩)
        rw [List.append_nil] at this
        rw [this]
        simpa [envWalk] using safeFor_fill (e :: es) ReceiveSpec.Class.structure rfl
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
        have := safeFor_true ((e :: es).take 10) ReceiveSpec.Class.structure rfl
          (fill ReceiveSpec.Class.error ((e :: es).drop 10))
        rwa [ht] at this

/-- **No payload byte of a delivered envelope is revealed (scanner level, every byte string).**
For every byte string `E` (the body of a delivered message, the envelope), every byte the
envelope walk reveals has a public class in the reference (`ReceiveSpec.envelope`, as
`ReceiveSpec.requestBody` applies it): a key, a length or a varint value, never a field's payload,
never a byte after the envelope left the protocol. -/
theorem envelope_payload_unrevealed (E : List Byte) :
    SafeFor (envWalk [] 0 0 E) (ReceiveSpec.envelope (E.length + 1) E) :=
  envWalk_safe (E.length + 1) E [] 0 0 hdrOK_nil (Nat.lt_succ_self _)

end ReceiveProofs
